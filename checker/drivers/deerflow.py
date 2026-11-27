"""lgtrace adapter for bytedance/deer-flow, pre-fix `00a90bb`, fix `2e05f38` (#2153) and the
two upstream commits that complete the fix, `da174dfd` and `c0da2782` (#2627).

DeerFlow is a research assistant that many users share through one server. Actors
- the user, a human, who sends a message in a thread of their own.
- `make_lead_agent`, plain code that builds the lead agent for each run. It reads the memory
  file and bakes its contents into the agent's system prompt.
- the lead agent, a langchain `create_agent` graph. Its `model` node is an LLM agent, its
  `tools` node plain code, and middleware nodes such as `MemoryMiddleware.after_agent` plain
  code. That middleware queues the conversation for the memory updater.
- `memory_updater`, an LLM agent that runs on a `threading.Timer` thread after the run, reads
  the queued conversation and the current memory, and saves new memory.

Before the fix one `memory.json` serves every user, so what user A says reaches the system
prompt of user B's lead agent (issue #1772). The fix keys memory files by user id, captured when
the conversation is queued. It lands in three steps upstream. Versions
- `pre`, `00a90bb`, venv `deerflow`.
- `commit`, `2e05f38`, venv `deerflow` (same dependencies). `MemoryUpdateQueue.add` passes
  `user_id` to `_enqueue_locked`, which does not take it, so every run crashes in
  `MemoryMiddleware.after_agent` (`queue.py:69`). `FileMemoryStorage` still keys its cache by
  agent name alone and loads the legacy file on a cache miss.
- `completed`, `da174dfd` (the same day), venv `deerflow-fixed` (langgraph 1.1.9). Its only
  memory changes fix the two faults above. `MemoryUpdater.update_memory` takes `user_id` but
  does not pass it on, so the updater still loads and saves the legacy shared `memory.json`,
  while lead agents read per-user files that nothing writes.
- `fixed`, `c0da2782` (2026-04-30), venv `deerflow-fixed`. It threads `user_id` through the
  updater, the first commit where memory is per user end to end.

State outside LangGraph and how it is recorded
- The memory store, through `lgtrace.recorded` on `FileMemoryStorage.load`, `reload` and
  `save`, as channel `ext:memory`. This is the app's own storage interface, which sits above
  its in-process cache. A load served from the cache opens no file.
- Files under DeerFlow's home directory, through `lgtrace.FileRecorder`, as `file:<path>`.
  Alone it finds nothing before the fix (`--seams file`), since B's load is a cache hit, and
  `lgtrace.unexplained` reports the flows it left without a path.
- The update queue, through a `lgtrace.Handoff` on `MemoryUpdateQueue.add` and `add_nowait`
  and on the updater's innermost entry (`updater_entry`), as `queue:memory`. The Timer thread
  starts with an empty context, so the updater is attributed to the task that queued the
  conversation, not to whatever context variable happens to be visible.
- The system prompt, through `apply_prompt_template`, as `built:lead_agent`. The `model` node
  reads it from its closure, which `lgtrace.built_reads` sees in the fake LLM's input.

Runs are one message each from user A (the attacker), user B, and A again, each in a thread of
its own, on one process. A's second run shows whether memory still reaches its own user, so a
fix that cuts memory off is told apart from one that isolates it. Every LLM choice of the lead
agent (reply, or web search then reply) and of the memory updater (a fact, a summary, a fact
below the confidence threshold, nothing) is enumerated. Each run waits for the memory queue to
drain, so the next run starts after the update. The web search tool is an offline stub.

The versions share the package name `deerflow`, so each runs in its own process, and `main`
starts one per version in that version's venv.
"""

from __future__ import annotations

import argparse
import functools
import inspect
import json
import os
import subprocess
import sys
import tempfile
import time
import traceback
import types
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from drivers import PY_DIR, VENVS_DIR, emit_json, on_path, options, report, repo, run_order
import lgtrace
from lgtrace import Run, Script, Subject, make_markers, marker_llm, router_scripts, seq

NAME = "deerflow"
REPOS = {"pre": "deer-flow", "commit": "deer-flow-2e05f38", "completed": "deer-flow-da174dfd",
         "fixed": "deer-flow-fixed"}
VENVS = {"pre": "deerflow", "commit": "deerflow", "completed": "deerflow-fixed",
         "fixed": "deerflow-fixed"}
NAMES = {"pre": NAME, "commit": f"{NAME}-2e05f38", "completed": f"{NAME}-da174dfd",
         "fixed": f"{NAME}-fixed"}
WRITES = frozenset({"pre", "completed", "fixed"})
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"A"})
MEMORY = "ext:memory"
QUEUE = "queue:memory"
BUILT = "built:lead_agent"
DRAIN_SECONDS = 60.0
SEAMS = ("storage", "file")

MEMORY_REPLIES: Mapping[str, str] = {
  "fact": json.dumps({"newFacts": [{"content": "The user said {markers}", "category": "context",
                                    "confidence": 0.9}]}),
  "summary": json.dumps({"user": {"topOfMind": {"shouldUpdate": True,
                                                "summary": "Asked about {markers}"}}}),
  "low": json.dumps({"newFacts": [{"content": "Maybe {markers}", "confidence": 0.5}]}),
  "none": json.dumps({"ignored": "{markers}"}),
}
LEAD_CALLS: Mapping[str, Any] = {
  "reply": [],
  "search": seq([{"name": "web_search", "args": {"query": "{markers}"}}], []),
}
CHOICES: Mapping[str, tuple[str, ...]] = {"lead": tuple(LEAD_CALLS),
                                          "memory": tuple(MEMORY_REPLIES)}
SEARCH_RESULT = "DeerFlow is an open-source research assistant."

CONFIG = """\
config_version: 8
log_level: warning
token_usage:
  enabled: false
models:
  - name: fake
    display_name: fake
    use: langchain_openai:ChatOpenAI
    model: fake
    api_key: none
    supports_thinking: false
    supports_vision: false
tools:
  - name: web_search
    group: web
    use: drivers.deerflow:web_search_stub
tool_groups:
  - name: web
tool_search:
  enabled: false
sandbox:
  use: deerflow.sandbox.local:LocalSandboxProvider
  allow_host_bash: false
title:
  enabled: true
  max_words: 6
  max_chars: 60
summarization:
  enabled: false
memory:
  enabled: true
  storage_path: memory.json
  debounce_seconds: 1
  max_facts: 100
  fact_confidence_threshold: 0.7
  injection_enabled: true
  max_injection_tokens: 2000
agents_api:
  enabled: false
"""


def scripts() -> tuple[dict[str, str], ...]:
  return router_scripts(CHOICES)


def __getattr__(name: str) -> Any:
  """`web_search_stub`, the offline web search the config names, built on first use."""
  if name == "web_search_stub":
    return web_search_tool()
  raise AttributeError(name)


@functools.cache
def web_search_tool() -> Any:
  from langchain_core.tools import tool

  @tool("web_search")
  def web_search(query: str) -> str:
    """Search the web."""
    return SEARCH_RESULT
  return web_search


# ---------------------------------------------------------------------------------------------
# Recording seams


@dataclass
class Current:
  """What the patched model factories hand out for the script being traced."""
  markers: Mapping[str, str]
  script: Script


CURRENT = Current({}, {})
HANDOFF = lgtrace.Handoff(QUEUE)


def llm_for(role: str) -> Callable[..., Any]:
  def make(*args: Any, **kwargs: Any) -> Any:
    script = CURRENT.script
    by_role = {
      "lead": {"text": "[fake] {markers}", "tool_calls": LEAD_CALLS[script["lead"]]},
      "memory": {"text": MEMORY_REPLIES[script["memory"]]},
      "title": {"text": "Title"},
    }
    return marker_llm(CURRENT.markers, by_role[role])
  return make


def thread_key(args: tuple[Any, ...], kwargs: Mapping[str, Any]) -> Any:
  return kwargs.get("thread_id", args[1] if len(args) > 1 else None)


def messages_of(args: tuple[Any, ...], kwargs: Mapping[str, Any]) -> Any:
  return kwargs.get("messages", args[2] if len(args) > 2 else None)


def sending(add: Callable[..., Any]) -> Callable[..., Any]:
  @functools.wraps(add)
  def wrapper(*args: Any, **kwargs: Any) -> Any:
    HANDOFF.send(thread_key(args, kwargs), messages_of(args, kwargs))
    return add(*args, **kwargs)
  return wrapper


def receiving(update: Callable[..., Any]) -> Callable[..., Any]:
  """The updater's innermost entry, run as external task `memory_updater` for the queueing task.

  The context variable is set inside the function that does the load, the LLM call and the
  save, so it holds whichever thread runs it, and `asyncio.to_thread` carries it further.
  """
  if inspect.iscoroutinefunction(update):
    @functools.wraps(update)
    async def awrapper(self: Any, messages: Any, thread_id: Any = None, *args: Any,
                       **kwargs: Any) -> Any:
      with HANDOFF.receive(thread_id, "memory_updater", messages):
        return await update(self, messages, thread_id, *args, **kwargs)
    return awrapper

  @functools.wraps(update)
  def wrapper(self: Any, messages: Any, thread_id: Any = None, *args: Any, **kwargs: Any) -> Any:
    with HANDOFF.receive(thread_id, "memory_updater", messages):
      return update(self, messages, thread_id, *args, **kwargs)
  return wrapper


def updater_entry(cls: type) -> str:
  """`_do_update_memory_sync` from `c0da2782` on, which runs the whole update in one thread,
  and before it the `aupdate_memory` coroutine. Only one is wrapped, so `c0da2782`'s
  `aupdate_memory`, which calls `_do_update_memory_sync`, opens one updater task, not two."""
  return "_do_update_memory_sync" if hasattr(cls, "_do_update_memory_sync") else "aupdate_memory"


def baking(template: Callable[..., str]) -> Callable[..., str]:
  @functools.wraps(template)
  def wrapper(*args: Any, **kwargs: Any) -> str:
    prompt = template(*args, **kwargs)
    lgtrace.emit(BUILT, "write", prompt)
    return prompt
  return wrapper


@functools.cache
def subject_modules(version: str, seams: tuple[str, ...]) -> types.SimpleNamespace:
  """The DeerFlow modules of `version`, with the model factories stubbed and the seams wired.

  The first call fixes the version for the process, since both versions are `deerflow`.
  """
  if any(m == "deerflow" or m.startswith("deerflow.") for m in sys.modules):
    loaded = sys.modules["deerflow"].__file__ or ""
    if REPOS[version] not in Path(loaded).parts:
      raise RuntimeError(f"deerflow already imported from {loaded}, run each version alone")
  root = repo(REPOS[version]) / "backend"
  config = Path(tempfile.mkdtemp(prefix="lgtrace-deerflow-cfg-")) / "config.yaml"
  config.write_text(CONFIG)
  os.environ["DEER_FLOW_CONFIG_PATH"] = str(config)
  on_path(root / "packages" / "harness")
  import deerflow.agents.lead_agent.agent as agent
  import deerflow.agents.memory.queue as queue
  import deerflow.agents.memory.storage as storage
  import deerflow.agents.memory.updater as updater
  import deerflow.agents.middlewares.title_middleware as title
  import deerflow.config.paths as paths
  import deerflow.runtime.user_context as user_context

  agent.create_chat_model = llm_for("lead")
  updater.create_chat_model = llm_for("memory")
  title.create_chat_model = llm_for("title")
  agent.apply_prompt_template = baking(agent.apply_prompt_template)
  queue.MemoryUpdateQueue.add = sending(queue.MemoryUpdateQueue.add)
  queue.MemoryUpdateQueue.add_nowait = sending(queue.MemoryUpdateQueue.add_nowait)
  entry = updater_entry(updater.MemoryUpdater)
  setattr(updater.MemoryUpdater, entry, receiving(getattr(updater.MemoryUpdater, entry)))
  if "storage" in seams:
    cls = storage.FileMemoryStorage
    store_channel = lambda *a, **k: MEMORY  # noqa: E731, one store for every key
    cls.load = lgtrace.recorded(cls.load, "read", store_channel)
    cls.reload = lgtrace.recorded(cls.reload, "read", store_channel)
    cls.save = lgtrace.recorded(cls.save, "write", store_channel)
  return types.SimpleNamespace(agent=agent, queue=queue, storage=storage, paths=paths,
                               user_context=user_context)


# ---------------------------------------------------------------------------------------------
# Runs


@dataclass(frozen=True)
class User:
  id: str


@dataclass
class DeerFlowServer:
  """One script's server process. `stream` serves one run as the LangGraph server does, by
  building the lead agent for the run's user, then waits for the memory queue to drain."""
  mods: types.SimpleNamespace
  store: Any
  checkpointer: Any
  home: Path
  seams: tuple[str, ...]

  def drain(self) -> None:
    q = self.mods.queue.get_memory_queue()
    deadline = time.monotonic() + DRAIN_SECONDS
    while q.pending_count or q.is_processing:
      if time.monotonic() > deadline:
        raise TimeoutError("memory queue did not drain")
      time.sleep(0.01)

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    """The run's events. The runtime context is the gateway worker's (`runs/worker.py`). An
    exception of the app ends the run and is kept in `CRASHES`."""
    user = config["configurable"]["lgtrace_user"]
    token = self.mods.user_context.set_current_user(User(user))
    files = lgtrace.FileRecorder(self.home) if "file" in self.seams else None
    try:
      if files:
        files.__enter__()
      with lgtrace.acting("make_lead_agent"):
        built = self.mods.agent.make_lead_agent(config)
      graph = lgtrace.instrument_compiled(built, checkpointer=self.checkpointer,
                                          store=self.store)
      context = {"thread_id": config["configurable"]["thread_id"],
                 "run_id": f"run-{len(CRASHES)}-{time.monotonic_ns()}"}
      try:
        yield from graph.stream(inp, config, context=context, **kwargs)
      except Exception as e:  # noqa: BLE001, the app's own crash ends the run
        CRASHES.append(crash_site(e))
      self.drain()
    finally:
      if files:
        files.__exit__(None, None, None)
      self.mods.user_context.reset_current_user(token)


CRASHES: list[str] = []


def crash_site(e: BaseException) -> str:
  frame = traceback.extract_tb(e.__traceback__)[-1]
  where = f"{Path(frame.filename).parent.name}/{Path(frame.filename).name}:{frame.lineno}"
  return f"{type(e).__name__} at {where}: {e}"


def build(version: str, markers: Mapping[str, str],
          seams: tuple[str, ...]) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    from langgraph.checkpoint.memory import InMemorySaver
    mods = subject_modules(version, seams)
    home = Path(tempfile.mkdtemp(prefix="lgtrace-deerflow-home-"))
    os.environ["DEER_FLOW_HOME"] = str(home)
    mods.paths._paths = None
    mods.storage._storage_instance = None
    mods.queue.reset_memory_queue()
    CURRENT.markers, CURRENT.script = markers, script
    return DeerFlowServer(mods, store, InMemorySaver(), home, seams)
  return go


def message(principal: str, marker: str) -> dict[str, Any]:
  return {"messages": [{"role": "user",
                        "content": f"Hi, I am user {principal}. Please remember {marker}"}]}


def make_subject(version: str, seams: tuple[str, ...] = SEAMS) -> Subject:
  markers = make_markers(PRINCIPALS)
  runs = tuple(Run(message(p, markers[p]), p,
                   {"configurable": {"thread_id": f"thread-{p}{i}", "lgtrace_user": p,
                                     "thinking_enabled": False},
                    "recursion_limit": 50})
               for i, p in enumerate(run_order(PRINCIPALS, ATTACKERS)))
  return Subject(build(version, markers, seams), runs, markers, ATTACKERS, scripts())


def subject(seams: tuple[str, ...] = SEAMS) -> Subject:
  return make_subject("pre", seams)


def commit_subject(seams: tuple[str, ...] = SEAMS) -> Subject:
  return make_subject("commit", seams)


def fixed_subject(seams: tuple[str, ...] = SEAMS) -> Subject:
  return make_subject("fixed", seams)


# ---------------------------------------------------------------------------------------------
# Entry point


def one(version: str, seams: tuple[str, ...], rest: list[str]) -> None:
  opts = options(rest)
  name = NAMES[version] + ("" if seams == SEAMS else "-" + "+".join(seams))
  write = opts.write and seams == SEAMS and version in WRITES
  summary = report(name, opts.narrow(make_subject(version, seams)), write)
  summary["crashes"] = {c: CRASHES.count(c) for c in sorted(set(CRASHES))}
  print("".join(f"app crash in {n} runs: {c}\n" for c, n in summary["crashes"].items()), end="")
  emit_json([summary])


def main() -> None:
  ap = argparse.ArgumentParser()
  ap.add_argument("--version", choices=tuple(REPOS), help="one version, in this process")
  ap.add_argument("--seams", default=",".join(SEAMS))
  args, rest = ap.parse_known_args()
  seams = tuple(s for s in args.seams.split(",") if s)
  if args.version:
    one(args.version, seams, rest)
    return
  summaries = []
  for version in REPOS:
    python = VENVS_DIR / VENVS[version] / "bin" / "python"
    proc = subprocess.run([str(python), "-m", "drivers.deerflow", "--version", version,
                           "--seams", args.seams, *rest], cwd=PY_DIR, capture_output=True,
                          text=True)
    print("".join(ln + "\n" for ln in proc.stdout.splitlines()
                  if not ln.startswith("LGTRACE_JSON ")), end="")
    if proc.returncode:
      print(proc.stderr[-4000:], file=sys.stderr)
      raise SystemExit(proc.returncode)
    line = next(ln for ln in proc.stdout.splitlines() if ln.startswith("LGTRACE_JSON "))
    summaries.extend(json.loads(line.removeprefix("LGTRACE_JSON ")))
  emit_json(summaries)


if __name__ == "__main__":
  main()
