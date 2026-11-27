"""`lgmonitor` on the real apps, DeerFlow and Yuxi, with the fake LLMs of their lgtrace adapters.

Each (subject, version, config) runs in its own process in the version's venv, since the
versions share a package name. A config is `baseline` (no monitor) or `<policy>-<mode>`, with
policy `iso` (the built-in isolation policy, nothing shared) or `spec` (the irspec
configuration `--spec`, by default the subject's fixed spec, at principal level) or
`specagent` (the same at agent level). Every script of the adapter runs, each on a fresh home
or save directory with a fresh monitor, with runs A, B, A as in the adapters.

What a run records
- the monitor's violations and unseen accesses, per run;
- for DeerFlow, the system prompt `make_lead_agent` built, and which users' markers it holds;
  for Yuxi, which users' markers the run's messages hold and whether a write was refused
  because the file already existed (a check `os.stat` makes, which no seam sees);
- app crashes, and wall time of the run, which for DeerFlow includes building and compiling
  the lead agent; DeerFlow also times `graph.stream` alone and the memory updater, which runs
  after a one second debounce on a timer thread and is timed inside it).

`python -m drivers.monitored` runs everything one process at a time and prints a table, and
`--json` writes the raw results.
"""

from __future__ import annotations

import argparse
import asyncio
import contextlib
import functools
import inspect
import json
import os
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
import traceback
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any

from drivers import PY_DIR, SPECS_DIR, VENVS_DIR, on_path, repo, run_order
import lgmonitor
from lgmonitor import Isolation, Monitor, MonitoredFiles, MonitoredHandoff, SpecPolicy
from lgtrace import leaves, make_markers

CONFIGS = ("baseline", "iso-block", "iso-flag", "spec-block", "specagent-flag")
NULL = contextlib.nullcontext()


def make_monitor(config: str, spec: Path) -> Monitor | None:
  if config == "baseline":
    return None
  policy_name, mode = config.split("-")
  policy = {"iso": lambda: Isolation(),
            "spec": lambda: SpecPolicy.from_spec(spec),
            "specagent": lambda: SpecPolicy.from_spec(spec, level="agent")}[policy_name]()
  return Monitor(policy, mode)  # type: ignore[arg-type]


def holders(value: Any, markers: Mapping[str, str]) -> list[str]:
  return sorted(p for p, m in markers.items() if any(m in t for t in leaves(value)))


def crash_site(e: BaseException) -> str:
  frame = traceback.extract_tb(e.__traceback__)[-1]
  return f"{type(e).__name__} at {Path(frame.filename).name}:{frame.lineno}: {e}"


def run_record(mon: Monitor | None, before: tuple[int, int]) -> dict[str, Any]:
  if mon is None:
    return {"violations": [], "unseen": []}
  return {"violations": [_v(v) for v in mon.violations[before[0]:]],
          "unseen": [_u(u) for u in mon.unseen[before[1]:]]}


def _v(v: lgmonitor.Violation) -> list[str]:
  return [v.seam, v.op, v.channel, v.key, v.agent, ",".join(v.writers), v.action]


def _u(u: lgmonitor.Unseen) -> list[str]:
  return [u.seam, u.event, u.channel, u.key, u.detail]


def marks(mon: Monitor | None) -> tuple[int, int]:
  return (len(mon.violations), len(mon.unseen)) if mon else (0, 0)


# ---------------------------------------------------------------------------------------------
# DeerFlow


class DeerFlow:
  """DeerFlow wired for the monitor. Only the model factories are stubbed, as in the adapter,
  and the monitor's seams replace the adapter's recorders. Seams consult `self.mon` and pass
  straight through when it is None, so one process can alternate monitored and baseline runs
  (`--overhead`). A plain baseline process installs none of them."""

  def __init__(self, version: str, monitored: bool) -> None:
    from drivers import deerflow as df
    self.df, self.version = df, version
    self.mon: Monitor | None = None
    self.prompts: list[str] = []
    self.update_seconds: list[float] = []
    self.stream_seconds: list[float] = []
    root = repo(df.REPOS[version]) / "backend"
    config = Path(tempfile.mkdtemp(prefix="lgmonitor-deerflow-cfg-")) / "config.yaml"
    config.write_text(df.CONFIG)
    os.environ["DEER_FLOW_CONFIG_PATH"] = str(config)
    on_path(root / "packages" / "harness")
    import deerflow.agents.lead_agent.agent as agent
    import deerflow.agents.memory.queue as queue
    import deerflow.agents.memory.storage as storage
    import deerflow.agents.memory.updater as updater
    import deerflow.agents.middlewares.title_middleware as title
    import deerflow.config.paths as paths
    import deerflow.runtime.user_context as user_context
    self.agent, self.queue, self.storage = agent, queue, storage
    self.paths, self.user_context = paths, user_context
    agent.create_chat_model = df.llm_for("lead")
    updater.create_chat_model = df.llm_for("memory")
    title.create_chat_model = df.llm_for("title")
    agent.apply_prompt_template = self.baking(agent.apply_prompt_template)
    entry = df.updater_entry(updater.MemoryUpdater)
    setattr(updater.MemoryUpdater, entry, self.timed(getattr(updater.MemoryUpdater, entry)))
    if monitored:
      self.wire(updater, entry)

  def baking(self, template: Callable[..., str]) -> Callable[..., str]:
    @functools.wraps(template)
    def wrapper(*args: Any, **kwargs: Any) -> str:
      prompt = template(*args, **kwargs)
      self.prompts.append(prompt)
      if self.mon:
        self.mon.built(self.df.BUILT, prompt)
      return prompt
    return wrapper

  def timed(self, update: Callable[..., Any]) -> Callable[..., Any]:
    if inspect.iscoroutinefunction(update):
      @functools.wraps(update)
      async def awrapper(*args: Any, **kwargs: Any) -> Any:
        t = time.perf_counter()
        try:
          return await update(*args, **kwargs)
        finally:
          self.update_seconds.append(time.perf_counter() - t)
      return awrapper

    @functools.wraps(update)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
      t = time.perf_counter()
      try:
        return update(*args, **kwargs)
      finally:
        self.update_seconds.append(time.perf_counter() - t)
    return wrapper

  def location(self, st: Any, *args: Any, **kwargs: Any) -> str:
    path = st._get_memory_file_path(*args, **kwargs)  # noqa: SLF001
    return os.path.relpath(path, self.home)

  def wire(self, updater: Any, entry: str) -> None:
    df, me = self.df, self
    cls = self.storage.FileMemoryStorage
    empty = lambda _v: me.storage.create_empty_memory()  # noqa: E731
    channel = lambda *a, **k: df.MEMORY  # noqa: E731
    read_key = lambda st, *a, **k: me.location(st, *a, **k)  # noqa: E731
    write_key = lambda st, data, *a, **k: me.location(st, *a, **k)  # noqa: E731

    def late(fn: Callable[..., Any], mode: str, key: Callable[..., str]) -> Callable[..., Any]:
      """`lgmonitor.guarded` against whichever monitor the current script uses."""
      @functools.wraps(fn)
      def wrapper(*args: Any, **kwargs: Any) -> Any:
        if me.mon is None:
          return fn(*args, **kwargs)
        g = lgmonitor.guarded(fn, me.mon, mode, channel, key, mask=empty)  # type: ignore
        return g(*args, **kwargs)
      return wrapper
    cls.load = late(cls.load, "read", read_key)
    cls.reload = late(cls.reload, "read", read_key)
    cls.save = late(cls.save, "write", write_key)

    self.handoff = MonitoredHandoff(df.QUEUE)

    def sending(add: Callable[..., Any]) -> Callable[..., Any]:
      @functools.wraps(add)
      def wrapper(*args: Any, **kwargs: Any) -> Any:
        if me.mon is None:
          return add(*args, **kwargs)
        me.handoff.monitor = me.mon
        me.handoff.send(df.thread_key(args, kwargs), df.messages_of(args, kwargs))
        return add(*args, **kwargs)
      return wrapper
    self.queue.MemoryUpdateQueue.add = sending(self.queue.MemoryUpdateQueue.add)
    self.queue.MemoryUpdateQueue.add_nowait = sending(self.queue.MemoryUpdateQueue.add_nowait)

    update = getattr(updater.MemoryUpdater, entry)
    if inspect.iscoroutinefunction(update):
      @functools.wraps(update)
      async def areceiving(self_: Any, messages: Any, thread_id: Any = None, *args: Any,
                           **kwargs: Any) -> Any:
        if me.mon is None:
          return await update(self_, messages, thread_id, *args, **kwargs)
        with me.handoff.receive_value(thread_id, "memory_updater", messages) as got:
          return await update(self_, got, thread_id, *args, **kwargs)
      setattr(updater.MemoryUpdater, entry, areceiving)
    else:
      @functools.wraps(update)
      def receiving(self_: Any, messages: Any, thread_id: Any = None, *args: Any,
                    **kwargs: Any) -> Any:
        if me.mon is None:
          return update(self_, messages, thread_id, *args, **kwargs)
        with me.handoff.receive_value(thread_id, "memory_updater", messages) as got:
          return update(self_, got, thread_id, *args, **kwargs)
      setattr(updater.MemoryUpdater, entry, receiving)

  def reset(self, mon: Monitor | None) -> None:
    from langgraph.checkpoint.memory import InMemorySaver
    from langgraph.store.memory import InMemoryStore
    self.mon = mon
    self.home = Path(tempfile.mkdtemp(prefix="lgmonitor-deerflow-home-"))
    os.environ["DEER_FLOW_HOME"] = str(self.home)
    self.paths._paths = None  # noqa: SLF001
    self.storage._storage_instance = None  # noqa: SLF001
    self.queue.reset_memory_queue()
    self.checkpointer = InMemorySaver()
    self.store = lgmonitor.monitored_store(mon, InMemoryStore()) if mon else InMemoryStore()

  def drain(self) -> None:
    q = self.queue.get_memory_queue()
    deadline = time.monotonic() + self.df.DRAIN_SECONDS
    while q.pending_count or q.is_processing:
      if time.monotonic() > deadline:
        raise TimeoutError("memory queue did not drain")
      time.sleep(0.01)

  def serve(self, user: str, thread: str, inp: Any) -> tuple[float, str | None]:
    mon = self.mon
    config = {"configurable": {"thread_id": thread, "thinking_enabled": False},
              "recursion_limit": 50}
    token = self.user_context.set_current_user(self.df.User(user))
    crash = None
    files = MonitoredFiles(self.home, mon) if mon else NULL
    t0 = time.perf_counter()
    try:
      with files, (mon.serving(user) if mon else NULL):
        try:
          with mon.acting("make_lead_agent") if mon else NULL:
            built = self.agent.make_lead_agent(config)
          overrides = {"checkpointer": self.checkpointer, "store": self.store}
          graph = (lgmonitor.monitor_compiled(built, mon, ("model",), **overrides) if mon
                   else lgmonitor.recompile_builder(built, **overrides))
          if mon:
            mon.label_input(thread, inp)
          context = {"thread_id": thread, "run_id": f"run-{time.monotonic_ns()}"}
          t1 = time.perf_counter()
          for _ in graph.stream(inp, config, context=context):
            pass
          self.stream_seconds.append(time.perf_counter() - t1)
        except Exception as e:  # noqa: BLE001, the app's crash ends the run
          crash = crash_site(e)
        elapsed = time.perf_counter() - t0
        self.drain()
    finally:
      self.user_context.reset_current_user(token)
    return elapsed, crash

  def script(self, script: Mapping[str, str], config: str, spec: Path) -> dict[str, Any]:
    df = self.df
    markers = make_markers(df.PRINCIPALS)
    mon = make_monitor(config, spec)
    self.reset(mon)
    df.CURRENT.markers, df.CURRENT.script = markers, dict(script)
    runs = []
    for i, user in enumerate(run_order(df.PRINCIPALS, df.ATTACKERS)):
      before, n_prompts, n_upd = marks(mon), len(self.prompts), len(self.update_seconds)
      n_stream = len(self.stream_seconds)
      seconds, crash = self.serve(user, f"thread-{user}{i}", df.message(user, markers[user]))
      prompt = self.prompts[n_prompts:]
      runs.append({"user": user, "seconds": seconds, "crash": crash,
                   "stream_seconds": sum(self.stream_seconds[n_stream:]),
                   "update_seconds": sum(self.update_seconds[n_upd:]),
                   "prompt_holds": holders(prompt, markers), **run_record(mon, before)})
    return {"script": dict(script), "runs": runs,
            "summary": mon.summary() | {"violations": len(mon.violations),
                                        "unseen": len(mon.unseen)} if mon else None}


# ---------------------------------------------------------------------------------------------
# Yuxi


class Yuxi:
  def __init__(self, version: str, monitored: bool) -> None:
    from drivers import yuxi as yx
    self.yx, self.version = yx, version
    self.save_dir = tempfile.mkdtemp(prefix="lgmonitor-yuxi-")
    self.mods = yx.subject_modules(version, self.save_dir)
    self.monitored = monitored

  def graph(self, mon: Monitor | None) -> Any:
    from deepagents.middleware.filesystem import FilesystemMiddleware
    from langchain.agents import create_agent
    from langgraph.checkpoint.memory import InMemorySaver
    agent = create_agent(model=self.yx.fake_chat_model(), system_prompt=self.mods.prompt.strip(),
                         middleware=[FilesystemMiddleware(
                           backend=self.mods.composite.create_agent_composite_backend)])
    overrides = {"checkpointer": InMemorySaver()}
    return (lgmonitor.monitor_compiled(agent, mon, **overrides) if mon
            else lgmonitor.recompile_builder(agent, **overrides))

  def serve(self, graph: Any, mon: Monitor | None, user: str, thread: str,
            inp: Any) -> tuple[float, str | None, Any]:
    yx = self.yx
    yx.CURRENT.choice = ("read" if thread == yx.LAST_THREAD
                         else yx.CURRENT.script[f"tool_{user}"])
    config = {"configurable": {"thread_id": thread, "user_id": user}, "recursion_limit": 25}
    context = self.mods.context()
    context.update_from_dict({"user_id": user, "thread_id": thread})
    crash = None

    async def collect() -> None:
      async for _ in graph.astream(inp, config, context=context):
        pass
    t0 = time.perf_counter()
    with (MonitoredFiles(self.save_dir, mon) if mon else NULL), \
         (mon.serving(user) if mon else NULL):
      if mon:
        mon.label_input(thread, inp)
      try:
        asyncio.run(collect())
      except Exception as e:  # noqa: BLE001
        crash = crash_site(e)
    elapsed = time.perf_counter() - t0
    messages = graph.get_state(config).values.get("messages", [])
    return elapsed, crash, messages

  def script(self, script: Mapping[str, str], config: str, spec: Path) -> dict[str, Any]:
    yx = self.yx
    markers = make_markers(yx.PRINCIPALS)
    mon = make_monitor(config, spec)
    shutil.rmtree(Path(self.save_dir) / "threads", ignore_errors=True)
    yx.CURRENT.markers, yx.CURRENT.script = markers, dict(script)
    graph = self.graph(mon)
    runs = []
    for i, user in enumerate(yx.RUNS):
      before = marks(mon)
      inp = {"messages": [{"role": "user", "content": f"I am user {user}. {markers[user]}"}]}
      seconds, crash, messages = self.serve(graph, mon, user, f"thread-{user}{i}", inp)
      tools = [m.content for m in messages if getattr(m, "type", "") == "tool"]
      runs.append({"user": user, "seconds": seconds, "crash": crash,
                   "tool_holds": holders(tools, markers),
                   "exists_refused": any("already exists" in str(t) for t in tools),
                   "tool_results": [str(t)[:160] for t in tools],
                   **run_record(mon, before)})
    return {"script": dict(script), "runs": runs,
            "summary": mon.summary() | {"violations": len(mon.violations),
                                        "unseen": len(mon.unseen)} if mon else None}


# ---------------------------------------------------------------------------------------------
# Driver

SUBJECTS: Mapping[str, Mapping[str, Any]] = {
  "deerflow": {"versions": ("pre", "completed", "fixed"),
               "venv": lambda v: {"pre": "deerflow"}.get(v, "deerflow-fixed"),
               "spec": SPECS_DIR / "deerflow-fixed.json"},
  "yuxi": {"versions": ("pre", "fixed"), "venv": lambda v: "yuxi",
           "spec": SPECS_DIR / "yuxi-fixed.json"},
}


def one(subject: str, version: str, config: str, spec: Path) -> dict[str, Any]:
  monitored = config != "baseline"
  if subject == "deerflow":
    from drivers import deerflow as df
    app: Any = DeerFlow(version, monitored)
    scripts = df.scripts()
  else:
    from drivers import yuxi as yx
    app = Yuxi(version, monitored)
    scripts = yx.scripts()
  results = [app.script(s, config, spec) for s in scripts]
  return {"subject": subject, "version": version, "config": config, "scripts": results}


def overhead(subject: str, version: str, rounds: int, spec: Path) -> dict[str, Any]:
  """Baseline and `iso-block` runs alternated in one process, wiring installed in both, so
  the difference is the monitor's own work. The order flips every round."""
  if subject == "deerflow":
    from drivers import deerflow as df
    app: Any = DeerFlow(version, True)
    scripts = df.scripts()
  else:
    from drivers import yuxi as yx
    app = Yuxi(version, True)
    scripts = yx.scripts()
  secs: dict[str, list[float]] = {"baseline": [], "iso-block": []}
  upd: dict[str, list[float]] = {"baseline": [], "iso-block": []}
  stream: dict[str, list[float]] = {"baseline": [], "iso-block": []}
  for r in range(rounds):
    order = ("baseline", "iso-block") if r % 2 == 0 else ("iso-block", "baseline")
    for s in scripts:
      for config in order:
        out = app.script(s, config, spec)
        secs[config].extend(run["seconds"] for run in out["runs"])
        upd[config].extend(run["update_seconds"] for run in out["runs"]
                           if run.get("update_seconds"))
        stream[config].extend(run.get("stream_seconds", run["seconds"]) for run in out["runs"])
  return {"subject": subject, "version": version, "rounds": rounds,
          "seconds": secs, "update_seconds": upd, "stream_seconds": stream}


def table(results: list[dict[str, Any]]) -> str:
  rows = []
  for r in results:
    runs = [run for s in r["scripts"] for run in s["runs"]]
    secs = [run["seconds"] for run in runs]
    viol = [tuple(v) for run in runs for v in run["violations"]]
    rows.append({
      "subject": r["subject"], "version": r["version"], "config": r["config"],
      "runs": len(runs), "crashes": sum(1 for run in runs if run["crash"]),
      "violations": len(viol),
      "channels": sorted({f"{v[0]}:{v[2]}[{v[3]}] {v[5]}->{v[4]} {v[6]}" for v in viol}),
      "unseen": sorted({" ".join(u) for run in runs for u in run["unseen"]}),
      "median_s": statistics.median(secs), "mean_s": statistics.fmean(secs),
      "update_median_s": (statistics.median(u) if (u := [run["update_seconds"] for run in runs
                                                         if "update_seconds" in run])
                          else None),
    })
  return json.dumps(rows, indent=1)


def main() -> None:
  ap = argparse.ArgumentParser()
  ap.add_argument("--subject", choices=tuple(SUBJECTS))
  ap.add_argument("--version")
  ap.add_argument("--config", default=None)
  ap.add_argument("--spec", type=Path)
  ap.add_argument("--json", type=Path, help="write all results here")
  ap.add_argument("--overhead", type=int, default=0, metavar="ROUNDS",
                  help="alternate baseline and iso-block in one process per version")
  ap.add_argument("--child", action="store_true", help=argparse.SUPPRESS)
  args = ap.parse_args()
  if args.overhead and args.child:
    spec = args.spec or SUBJECTS[args.subject]["spec"]
    print("LGMONITOR_JSON " + json.dumps(overhead(args.subject, args.version, args.overhead,
                                                  spec)))
    return
  if args.overhead:
    out = []
    for subject, info in SUBJECTS.items():
      if args.subject and subject != args.subject:
        continue
      for version in info["versions"]:
        if args.version and version != args.version:
          continue
        python = VENVS_DIR / info["venv"](version) / "bin" / "python"
        print(f"overhead {subject} {version}", file=sys.stderr, flush=True)
        proc = subprocess.run([str(python), "-m", "drivers.monitored", "--subject", subject,
                               "--version", version, "--overhead", str(args.overhead), "--child"],
                              cwd=PY_DIR, capture_output=True, text=True)
        if proc.returncode:
          print(proc.stderr[-4000:], file=sys.stderr)
          raise SystemExit(proc.returncode)
        line = next(ln for ln in proc.stdout.splitlines() if ln.startswith("LGMONITOR_JSON "))
        r = json.loads(line.removeprefix("LGMONITOR_JSON "))
        out.append(r)
        med = {c: statistics.median(v) for c, v in r["seconds"].items()}
        umed = {c: statistics.median(v) for c, v in r["update_seconds"].items() if v}
        smed = {c: statistics.median(v) for c, v in r["stream_seconds"].items()}
        print(json.dumps({"subject": subject, "version": version, "runs": len(r["seconds"]
                          ["baseline"]), "median_s": med, "update_median_s": umed,
                          "stream_median_s": smed,
                          "ratio": med["iso-block"] / med["baseline"],
                          "stream_ratio": smed["iso-block"] / smed["baseline"]}))
    if args.json:
      args.json.write_text(json.dumps(out, indent=1) + "\n")
    return
  if args.subject and args.version and args.config:
    spec = args.spec or SUBJECTS[args.subject]["spec"]
    print("LGMONITOR_JSON " + json.dumps(one(args.subject, args.version, args.config, spec)))
    return
  results = []
  for subject, info in SUBJECTS.items():
    if args.subject and subject != args.subject:
      continue
    for version in info["versions"]:
      if args.version and version != args.version:
        continue
      for config in (args.config,) if args.config else CONFIGS:
        python = VENVS_DIR / info["venv"](version) / "bin" / "python"
        cmd = [str(python), "-m", "drivers.monitored", "--subject", subject, "--version",
               version, "--config", config]
        print(f"running {subject} {version} {config}", file=sys.stderr, flush=True)
        proc = subprocess.run(cmd, cwd=PY_DIR, capture_output=True, text=True)
        if proc.returncode:
          print(proc.stderr[-4000:], file=sys.stderr)
          raise SystemExit(proc.returncode)
        line = next(ln for ln in proc.stdout.splitlines() if ln.startswith("LGMONITOR_JSON "))
        results.append(json.loads(line.removeprefix("LGMONITOR_JSON ")))
  if args.json:
    args.json.write_text(json.dumps(results, indent=1) + "\n")
  print(table(results))


if __name__ == "__main__":
  main()
