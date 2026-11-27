"""lgtrace adapter for JoshuaC215/agent-service-toolkit, thread hijacking (#305, #355).

The toolkit is a FastAPI service that serves LangGraph agents to many users. Actors
- the user, a human, who sends a message with a `thread_id` and a `user_id` through the
  Streamlit app or the HTTP API. Both ids are chosen by the client.
- `_handle_input` (`src/service/service.py`), plain code that builds the run config from the
  request, and from `54d5e89` on checks who owns the thread.
- the default agent, `research-assistant` (`src/agents/research_assistant.py`). `guard_input`
  is plain code here (LlamaGuard is skipped without a Groq key), `model` is an LLM agent with a
  web search and a calculator, and `tools` is plain code that runs them.

The service keeps one checkpointer for every user, addressed by `thread_id` alone. A user who
learns another user's `thread_id` can post into that thread, and the owner's next turn reads
the post (the IDOR reported in #305). Versions, each a checkout of the repo
- `pre`, `6aabc5e`, the parent of the fix. No check.
- `check`, `54d5e89` (#305). The check reads the owner from `state.config`, which a checkpointer
  never fills with `user_id`, so it never fires (found and said in #355).
- `metadata`, `1a1da86` (second commit of PR #355). The check reads `state.metadata`, so a
  caller sending its own `user_id` is refused. The id is still the caller's word.
- `reverted`, `a561c88` (#355 as merged). The maintainer removed the check, arguing that a
  caller-asserted id is no access control and that `thread_id` is the shareable capability.

Runs, on one service process: user B's first turn in B's thread, user A's post into B's
thread, B's second turn, and A's turn in A's own thread. A, the attacker, picks the `user_id`
of its post (`as_user`): its own id, B's id (spoofed), or none, in which case `_handle_input`
draws a fresh uuid. Every LLM choice of `model` (reply, web search, calculator) is enumerated.
A run refused with HTTP 403 runs no graph and is counted in `refused`.

The packages `agents`, `core` and `service` are the same names in every version, so each
version runs in its own process, as in the deer-flow adapter. One venv serves all four, since
their `uv.lock` files are identical.
"""

from __future__ import annotations

import argparse
import asyncio
import functools
import json
import os
import subprocess
import sys
import types
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from drivers import PY_DIR, VENVS_DIR, emit_json, on_path, options, report, repo
import lgtrace
from lgtrace import Run, Script, Subject, make_markers, marker_llm, router_scripts

NAME = "agent_service_toolkit"
VENV = "agent-service-toolkit"
REPOS = {"pre": "agent-service-toolkit", "check": "agent-service-toolkit-54d5e89",
         "metadata": "agent-service-toolkit-1a1da86",
         "reverted": "agent-service-toolkit-a561c88"}
NAMES = {"pre": NAME, "check": f"{NAME}-54d5e89", "metadata": f"{NAME}-1a1da86",
         "reverted": f"{NAME}-a561c88"}
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"A"})
AS_USER = ("own", "victim", "none")
SEARCH_RESULT = "snippet: The toolkit serves LangGraph agents, link: https://example.com"
MODEL_CALLS: Mapping[str, list[dict[str, Any]]] = {
  "reply": [],
  "search": [{"name": "WebSearch", "args": {"query": "{markers}"}}],
  "calculator": [{"name": "Calculator", "args": {"expression": "6 * 7"}}],
}
CHOICES: Mapping[str, tuple[str, ...]] = {"as_user": AS_USER, "model": tuple(MODEL_CALLS)}


def scripts() -> tuple[dict[str, str], ...]:
  return router_scripts(CHOICES)


@dataclass(frozen=True)
class Post:
  """One request to the service, run as one lgtrace `Run`."""
  principal: str
  thread: str
  user_id: str | None
  text: str


def posts(script: Script, markers: Mapping[str, str]) -> tuple[Post, ...]:
  attack_id = {"own": "user-A", "victim": "user-B", "none": None}[script["as_user"]]
  return (Post("B", "thread-B", "user-B", f"I am user B. {markers['B']}"),
          Post("A", "thread-B", attack_id, f"Note from user A. {markers['A']}"),
          Post("B", "thread-B", "user-B", f"User B again. {markers['B']}"),
          Post("A", "thread-A", "user-A", f"I am user A. {markers['A']}"))


# ---------------------------------------------------------------------------------------------
# Modules and stubs


@dataclass
class Current:
  markers: Mapping[str, str]
  script: Script


CURRENT = Current({}, {})
REFUSED: list[str] = []


@functools.cache
def subject_modules(version: str) -> types.SimpleNamespace:
  """The service and the research assistant of `version`, with the model and search stubbed."""
  if "service" in sys.modules:
    loaded = sys.modules["service"].__file__ or ""
    if REPOS[version] not in Path(loaded).parts:
      raise RuntimeError(f"service already imported from {loaded}, run each version alone")
  os.environ.update(USE_FAKE_MODEL="true", LANGFUSE_TRACING="false",
                    LANGCHAIN_TRACING_V2="false")
  for key in ("GROQ_API_KEY", "OPENWEATHERMAP_API_KEY"):
    os.environ.pop(key, None)
  on_path(repo(REPOS[version]) / "src")
  from langchain_community.tools import DuckDuckGoSearchResults
  DuckDuckGoSearchResults._run = lambda self, *a, **k: (SEARCH_RESULT, [])
  import agents.research_assistant as ra
  import service.service as service
  from fastapi import HTTPException
  from schema import UserInput
  ra.get_model = lambda *a, **k: FakeModel()
  return types.SimpleNamespace(ra=ra, service=service, HTTPException=HTTPException,
                               UserInput=UserInput)


class FakeModel:
  """The chat model `get_model` returns. Its tool call depends on the turn, so each call builds
  a fresh `marker_llm`: the scripted call after a human message, a plain reply after a tool."""

  def bind_tools(self, tools: Any, **kwargs: Any) -> Any:
    from langchain_core.messages import ToolMessage
    from langchain_core.runnables import RunnableLambda

    def call(messages: Any) -> Any:
      after_tool = bool(messages) and isinstance(messages[-1], ToolMessage)
      calls = [] if after_tool else MODEL_CALLS[CURRENT.script["model"]]
      return marker_llm(CURRENT.markers, {"tool_calls": calls}).invoke(messages)
    return RunnableLambda(call)


# ---------------------------------------------------------------------------------------------
# The service


@dataclass
class Service:
  """One script's service process. `stream` serves one request as `/stream` does: it runs
  `_handle_input`, which may refuse it, then streams the agent with the config it built."""
  mods: types.SimpleNamespace
  agent: Any
  posts: Mapping[str, Post]

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    post = self.posts[inp["post"]]
    user_input = self.mods.UserInput(message=post.text, thread_id=post.thread,
                                     user_id=post.user_id)

    async def collect() -> list[Any]:
      try:
        handled, _ = await self.mods.service._handle_input(user_input, self.agent)
      except self.mods.HTTPException as e:
        REFUSED.append(f"{e.status_code} for post {inp['post']}")
        return []
      run_config = {**handled["config"], "recursion_limit": 25}
      return [ev async for ev in self.agent.astream(handled["input"], run_config, **kwargs)]
    yield from asyncio.run(collect())


def build(version: str, markers: Mapping[str, str]) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    from langgraph.checkpoint.memory import InMemorySaver
    mods = subject_modules(version)
    CURRENT.markers, CURRENT.script = markers, script
    agent = lgtrace.instrument_compiled(mods.ra.research_assistant,
                                        checkpointer=InMemorySaver(), store=store)
    return Service(mods, agent, {str(i): p for i, p in enumerate(posts(script, markers))})
  return go


def make_subject(version: str) -> Subject:
  markers = make_markers(PRINCIPALS)
  # `Subject.runs` is fixed, while a post's `user_id` depends on the script, so each run names
  # its post by index and `Service` looks it up. Principals, threads and texts agree.
  layout = posts({"as_user": "own"}, markers)
  runs = tuple(Run({"post": str(i), "text": p.text}, p.principal,
                   {"configurable": {"thread_id": p.thread}})
               for i, p in enumerate(layout))
  return Subject(build(version, markers), runs, markers, ATTACKERS, scripts())


# ---------------------------------------------------------------------------------------------
# Entry point


def one(version: str, rest: list[str], suffix: str = "") -> dict[str, Any]:
  opts = options(rest)
  REFUSED.clear()
  summary = report(NAMES[version] + suffix, opts.narrow(make_subject(version)),
                   opts.write or bool(suffix))
  summary["refused"] = {c: REFUSED.count(c) for c in sorted(set(REFUSED))}
  print("".join(f"refused in {n} scripts: {c}\n" for c, n in summary["refused"].items()), end="")
  return summary


def main() -> None:
  ap = argparse.ArgumentParser()
  ap.add_argument("--version", choices=tuple(REPOS), help="one version, in this process")
  args, rest = ap.parse_known_args()
  if args.version:
    summaries = [one(args.version, rest)]
    if args.version == "metadata" and not rest:
      summaries.append(one(args.version, ["--where", "as_user=own"], "-ownid"))
    emit_json(summaries)
    return
  summaries = []
  for version in REPOS:
    proc = subprocess.run([str(VENVS_DIR / VENV / "bin" / "python"), "-m",
                           "drivers.agent_service_toolkit", "--version", version, *rest],
                          cwd=PY_DIR, capture_output=True, text=True)
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
