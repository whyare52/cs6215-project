"""lgtrace adapter for xerrors/Yuxi, the shared sandbox workspace (#594).

Yuxi (语析) is a multi-user knowledge-base and agent platform. Its agents run in a sandbox with a
virtual file system under `/home/gem/user-data`, where `workspace/` holds working files that
the system prompt calls the user's directory. Actors
- the users A (the attacker) and B, humans who chat in threads of their own.
- the chatbot lead agent, a langchain `create_agent` graph (`agents/buildin/chatbot/graph.py`).
  Its `model` node is an LLM agent and its `tools` node plain code, including the file tools of
  deepagents' `FilesystemMiddleware`.
- `create_agent_composite_backend` (`agents/backends/composite.py`), plain code that builds
  each call's file backend from the run, and `sandbox/paths.py`, plain code that maps a virtual
  path to a host directory.

Before the fix `_global_user_data_dir()` is `save_dir/threads/shared` with no user in it, so
every user's `workspace/` is one directory and B's agent reads what A's agent wrote. The
maintainer called it a bug in #594. Versions
- `pre`, `db0dcb0d`. `workspace/` maps to `threads/shared/workspace`.
- `fixed`, `e0c6159c` (worktree `Yuxi-fixed`). `create_agent_composite_backend` reads
  `user_id` from the run and `workspace/` maps to `threads/shared/<user_id>/workspace`.

What runs. The gateway's run config (`services/chat_service.py:585`, thread and user ids),
the real chatbot system prompt, the real `FilesystemMiddleware(backend=
create_agent_composite_backend)` and the real path mapping. The sandbox provisioner, a docker
or k8s service, is replaced by deepagents' `FilesystemBackend` whose paths go through the
version's own `resolve_virtual_path`, which is the mapping the provisioner's bind mounts
implement (`docker/sandbox_provisioner/app.py`). The other middlewares (knowledge bases, MCP,
skills, subagents, summaries) are left out, so their paths are not covered.

Runs are A, B and A again, each in a thread of its own, on one save directory. In the first
two runs each user's agent, per its own scripted choice, writes a note to `workspace/notes.md`,
reads it, lists the workspace, or only replies. In A's second run it reads the note, which
shows whether a fix cuts A off from A's own workspace. Files are recorded by `lgtrace.FileRecorder` on the save directory,
as `file:<path>`.

Both versions are the package `yuxi`, so each runs in its own process, as in the deer-flow
adapter. One venv serves both.
"""

from __future__ import annotations

import argparse
import asyncio
import functools
import inspect
import json
import shutil
import os
import subprocess
import sys
import tempfile
import types
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from drivers import PY_DIR, VENVS_DIR, emit_json, on_path, options, report, repo, run_order
import lgtrace
from lgtrace import Run, Script, Subject, make_markers, marker_llm, router_scripts

NAME = "yuxi"
VENV = "yuxi"
REPOS = {"pre": "Yuxi", "fixed": "Yuxi-fixed"}
NAMES = {"pre": NAME, "fixed": f"{NAME}-fixed"}
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"A"})
RUNS = run_order(PRINCIPALS, ATTACKERS)
LAST_THREAD = f"thread-{RUNS[-1]}{len(RUNS) - 1}"
NOTE = "/home/gem/user-data/workspace/notes.md"
TOOLS: Mapping[str, list[dict[str, Any]]] = {
  "write": [{"name": "write_file", "args": {"file_path": NOTE, "content": "Notes {markers}"}}],
  "read": [{"name": "read_file", "args": {"file_path": NOTE}}],
  "ls": [{"name": "ls", "args": {"path": "/home/gem/user-data/workspace"}}],
  "reply": [],
}
CHOICES = {f"tool_{p}": tuple(TOOLS) for p in PRINCIPALS}


def scripts() -> tuple[dict[str, str], ...]:
  return router_scripts(CHOICES)


@dataclass
class Current:
  markers: Mapping[str, str]
  script: Script
  choice: str = ""


CURRENT = Current({}, {})


class FakeModel:
  """The lead agent's model. Its tool call depends on the step and on whose run it serves, so
  each call builds a fresh `marker_llm`: the scripted tool after the user's message, a reply
  after a tool result."""

  def bind_tools(self, tools: Any, **kwargs: Any) -> Any:
    from langchain_core.messages import ToolMessage
    from langchain_core.runnables import RunnableLambda

    def call(messages: Any) -> Any:
      after_tool = bool(messages) and isinstance(messages[-1], ToolMessage)
      calls = [] if after_tool else TOOLS[CURRENT.choice]
      return marker_llm(CURRENT.markers, {"tool_calls": calls}).invoke(messages)
    return RunnableLambda(call)


def fake_chat_model() -> Any:
  """A `BaseChatModel`, as `create_agent` requires, whose `bind_tools` is `FakeModel`'s."""
  llm = marker_llm({})
  object.__setattr__(llm, "bind_tools", FakeModel().bind_tools)
  return llm


def sandbox_class(paths: types.ModuleType) -> type:
  """The stand-in for `ProvisionerSandboxBackend`, a `FilesystemBackend` on the host whose
  virtual paths go through the version's `resolve_virtual_path`."""
  from deepagents.backends.filesystem import FilesystemBackend
  takes_user = "user_id" in inspect.signature(paths.resolve_virtual_path).parameters

  class HostSandbox(FilesystemBackend):
    def __init__(self, thread_id: str, *, user_id: str | None = None,
                 visible_skills: list[str] | None = None) -> None:
      super().__init__(root_dir="/", virtual_mode=False)
      self.thread_id, self.user_id = thread_id, user_id

    def _resolve_path(self, key: str) -> Path:
      if not key.startswith(paths.get_virtual_path_prefix()):
        return super()._resolve_path(key)
      kwargs = {"user_id": self.user_id} if takes_user else {}
      target = paths.resolve_virtual_path(self.thread_id, key, **kwargs)
      ensure = paths.ensure_thread_dirs
      ensure(self.thread_id, self.user_id) if takes_user else ensure(self.thread_id)
      return target
  return HostSandbox


@functools.cache
def subject_modules(version: str, save_dir: str) -> types.SimpleNamespace:
  if "yuxi" in sys.modules:
    loaded = sys.modules["yuxi"].__file__ or ""
    if REPOS[version] not in Path(loaded).parts:
      raise RuntimeError(f"yuxi already imported from {loaded}, run each version alone")
  # `YUXI_SKIP_APP_INIT=1` is the app's own switch that keeps `yuxi.knowledge` from dialing
  # Neo4j and Milvus on import. The key only satisfies the provider check, no call is made.
  os.environ.update(SAVE_DIR=save_dir, OPENAI_API_KEY="unused-offline", YUXI_SKIP_APP_INIT="1")
  root = repo(REPOS[version]) / "backend" / "package"
  on_path(root)
  on_path(root.parent)  # `server.utils`, which `yuxi.storage` imports
  import yuxi.agents.backends.composite as composite
  import yuxi.agents.backends.sandbox.paths as paths
  from yuxi.agents.buildin.chatbot.prompt import PROMPT
  from yuxi.agents.context import BaseContext
  composite.ProvisionerSandboxBackend = sandbox_class(paths)
  return types.SimpleNamespace(composite=composite, paths=paths, prompt=PROMPT,
                               context=BaseContext)


@dataclass
class Server:
  """One script's server. `stream` serves one run as `BaseAgent.stream_messages` does, with
  the run context holding the thread and user ids, under a `FileRecorder` on the save dir."""
  graph: Any
  save_dir: str
  mods: types.SimpleNamespace

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    ids = config["configurable"]
    # A's second run always reads, which shows whether A's own note still reaches A
    CURRENT.choice = ("read" if ids["thread_id"] == LAST_THREAD
                      else CURRENT.script[f"tool_{ids['user_id']}"])
    context = self.mods.context()
    context.update_from_dict({"user_id": ids["user_id"], "thread_id": ids["thread_id"]})

    async def collect() -> list[Any]:
      return [ev async for ev in self.graph.astream(inp, config, context=context, **kwargs)]
    with lgtrace.FileRecorder(self.save_dir):
      events = asyncio.run(collect())
    yield from events


def build(version: str, markers: Mapping[str, str]) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    from deepagents.middleware.filesystem import FilesystemMiddleware
    from langchain.agents import create_agent
    from langgraph.checkpoint.memory import InMemorySaver
    save_dir = os.environ.setdefault("LGTRACE_YUXI_SAVE",
                                     tempfile.mkdtemp(prefix="lgtrace-yuxi-"))
    mods = subject_modules(version, save_dir)
    shutil.rmtree(Path(save_dir) / "threads", ignore_errors=True)  # fresh files per script
    CURRENT.markers, CURRENT.script = markers, script
    agent = create_agent(model=fake_chat_model(), system_prompt=mods.prompt.strip(),
                         middleware=[FilesystemMiddleware(
                           backend=mods.composite.create_agent_composite_backend)])
    graph = lgtrace.instrument_compiled(agent, checkpointer=InMemorySaver(), store=store)
    return Server(graph, save_dir, mods)
  return go


def make_subject(version: str) -> Subject:
  markers = make_markers(PRINCIPALS)
  runs = tuple(Run({"messages": [{"role": "user", "content": f"I am user {p}. {markers[p]}"}]},
                   p, {"configurable": {"thread_id": f"thread-{p}{i}", "user_id": p},
                       "recursion_limit": 25})
               for i, p in enumerate(RUNS))
  return Subject(build(version, markers), runs, markers, ATTACKERS, scripts())


def one(version: str, rest: list[str]) -> None:
  opts = options(rest)
  emit_json([report(NAMES[version], opts.narrow(make_subject(version)), opts.write)])


def main() -> None:
  ap = argparse.ArgumentParser()
  ap.add_argument("--version", choices=tuple(REPOS), help="one version, in this process")
  args, rest = ap.parse_known_args()
  if args.version:
    one(args.version, rest)
    return
  summaries = []
  for version in REPOS:
    proc = subprocess.run([str(VENVS_DIR / VENV / "bin" / "python"), "-m", "drivers.yuxi",
                           "--version", version, *rest], cwd=PY_DIR, capture_output=True,
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
