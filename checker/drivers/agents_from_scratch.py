"""lgtrace adapter for langchain-ai/agents-from-scratch `603fc7a`, HITL memory assistant.

Subject file `src/email_assistant/email_assistant_hitl_memory.py`. One graph run triages one
email for the user (a human), who answers interrupts in Agent Inbox. Actors
- `triage_router`, an LLM agent that classifies the email as ignore, notify or respond.
- `triage_interrupt_handler`, plain code that asks the human about a notify email.
- `response_agent/llm_call`, an LLM agent that picks a tool call.
- `response_agent/interrupt_handler`, plain code that asks the human to review a tool call and
  runs the tool. Both handlers call `update_memory`, an LLM that rewrites a profile in the store.

Runs are one email each, from sender A (the attacker) and then sender B, on one store. Every LLM
choice (classification, tool) and every human choice (notify and tool review answers) is
enumerated by `router_scripts`. The human is scripted by `HumanDriven`, which resumes each
interrupt with the scripted answer. The tools in `tools/default` are already offline stubs.

Needs the lockfile versions (langgraph 0.4.8). On langgraph 1.x the app crashes at `:51`.
"""

from __future__ import annotations

import functools
import sys
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from types import ModuleType
from typing import Any

from drivers import emit_json, on_path, options, report, repo
from lgtrace import (Run, Script, Subject, instrument, make_markers, marker_llm, router_scripts,
                     seq)

NAME = "agents_from_scratch"
REPO = "agents-from-scratch"
MODULE = "email_assistant.email_assistant_hitl_memory"
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"A"})
MAX_RESUMES = 10

TOOL_ARGS: Mapping[str, dict[str, Any]] = {
  "write_email": {"to": "sender@example.com", "subject": "Re: hello", "content": "{markers}"},
  "schedule_meeting": {"attendees": ["sender@example.com"], "subject": "Sync {markers}",
                       "duration_minutes": 30, "preferred_day": "2025-05-01T00:00:00",
                       "start_time": 14},
  "Question": {"content": "Should I reply? {markers}"},
  "check_calendar_availability": {"day": "Thursday {markers}"},
  "Done": {"done": True},
}
HITL_ANSWERS: Mapping[str, tuple[str, ...]] = {
  "write_email": ("accept", "edit", "ignore", "response"),
  "schedule_meeting": ("accept", "edit", "ignore", "response"),
  "Question": ("ignore", "response"),
}
CHOICES: Mapping[str, tuple[Any, ...]] = {
  "RouterSchema": tuple({"classification": c} for c in ("ignore", "notify", "respond")),
  "notify_human": ("ignore", "response"),
  "tool": tuple(TOOL_ARGS),
  "tool_human": ("accept", "edit", "ignore", "response"),
}


def relevant(choice: Mapping[str, Any]) -> tuple[tuple[str, Any], ...] | None:
  """The choices a script actually exercises, or None for a combination the app cannot reach.

  Question has no accept or edit in its Agent Inbox config, so those answers are unreachable.
  """
  route = choice["RouterSchema"]["classification"]
  agent_runs = route == "respond" or (route == "notify" and choice["notify_human"] == "response")
  keys = (["RouterSchema"] + (["notify_human"] if route == "notify" else [])
          + (["tool"] if agent_runs else []))
  if "tool" in keys and choice["tool"] in HITL_ANSWERS:
    if choice["tool_human"] not in HITL_ANSWERS[choice["tool"]]:
      return None
    keys.append("tool_human")
  return tuple((k, repr(choice[k])) for k in keys)


def scripts() -> tuple[dict[str, Any], ...]:
  """One script per reachable combination of LLM and human choices, without duplicates."""
  keyed = {key: s for s in router_scripts(CHOICES) if (key := relevant(s)) is not None}
  return tuple({k: s[k] for k, _ in key} for key, s in keyed.items())


def human_answer(script: Script, request: Mapping[str, Any]) -> list[dict[str, Any]]:
  """The scripted human's Agent Inbox answer to one interrupt request."""
  is_notify = request["action_request"]["action"].startswith("Email Assistant:")
  kind = script["notify_human" if is_notify else "tool_human"]
  args = {"accept": "", "ignore": "", "response": "Please keep it short.",
          "edit": {"args": request["action_request"]["args"]}}[kind]
  return [{"type": kind, "args": args}]


@dataclass(frozen=True)
class HumanDriven:
  """A compiled graph whose `stream` answers every interrupt like the scripted human."""
  graph: Any
  answer: Callable[[Mapping[str, Any]], Any]

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    from langgraph.types import Command
    yield from self.graph.stream(inp, config, **kwargs)
    for _ in range(MAX_RESUMES):
      pending = [i for t in self.graph.get_state(config, subgraphs=True).tasks
                 for i in t.interrupts]
      if not pending:
        return
      yield from self.graph.stream(Command(resume=self.answer(pending[0].value[0])), config,
                                   **kwargs)
    raise RuntimeError(f"more than {MAX_RESUMES} interrupts in one run")


@functools.cache
def subject_module() -> ModuleType:
  """The subject module, imported with `init_chat_model` stubbed so no provider is needed."""
  on_path(repo(REPO) / "src")
  import langchain.chat_models as chat_models
  chat_models.init_chat_model = lambda *a, **k: marker_llm({})
  __import__(MODULE)
  return sys.modules[MODULE]


def llm_script(script: Script) -> dict[str, Any]:
  call = {"name": script["tool"], "args": TOOL_ARGS[script["tool"]]} if "tool" in script else None
  done = {"name": "Done", "args": TOOL_ARGS["Done"]}
  return {"RouterSchema": script["RouterSchema"],
          "tool_calls": seq([call or done], [done])}


def build(markers: Mapping[str, str]) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    from langgraph.checkpoint.memory import InMemorySaver
    mod = subject_module()
    llm = marker_llm(markers, llm_script(script))
    mod.llm_router = llm.with_structured_output(mod.RouterSchema)
    mod.llm_with_tools = llm.bind_tools(mod.tools, tool_choice="required")
    mod.init_chat_model = lambda *a, **k: llm
    graph = instrument(mod.overall_workflow).compile(store=store, checkpointer=InMemorySaver())
    return HumanDriven(graph, functools.partial(human_answer, script))
  return go


def email(principal: str, marker: str) -> dict[str, Any]:
  return {"email_input": {
    "author": f"Sender {principal} <{principal.lower()}@example.com>",
    "to": "Lance Martin <lance@company.com>",
    "subject": f"Message from {principal}",
    "email_thread": f"Hi Lance, a note from {principal}. {marker}",
  }}


def subject() -> Subject:
  markers = make_markers(PRINCIPALS)
  runs = tuple(Run(email(p, markers[p]), p, {"configurable": {"thread_id": f"thread-{p}"}})
               for p in PRINCIPALS)
  return Subject(build(markers), runs, markers, ATTACKERS, scripts())


def main() -> None:
  opts = options()
  emit_json([report(NAME, opts.narrow(subject()), opts.write)])


if __name__ == "__main__":
  main()
