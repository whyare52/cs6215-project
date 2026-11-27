"""lgtrace adapter for langchain-ai/executive-ai-assistant (EAIA) `758db71`.

EAIA answers one person's email. It runs on the LangGraph platform with one store, and every
incoming email is one run of graph `main` in a thread of its own. Actors
- the senders A (the attacker) and B, humans who write to the owner.
- the owner, a human, who answers interrupts in Agent Inbox (accept, edit, ignore, respond).
- `triage_input`, an LLM agent that labels the email `no`, `email`, `notify` or `question`.
  Its prompt holds up to five past emails found by semantic search in the store namespace
  `(assistant_id, "triage_examples")` (`main/fewshot.py:32-40`).
- `draft_response`, an LLM agent that picks a tool (reply draft, question to the owner,
  meeting assistant, calendar invite), with preferences read from the store namespace
  `(assistant_id,)`. `rewrite`, an LLM agent, restyles a draft with `rewrite_instructions`.
- `find_meeting_time`, an LLM agent (a ReAct agent over the calendar).
- `notify`, `send_message`, `send_email_draft`, `send_cal_invite`, plain code that interrupts
  for the owner. With `memory: true` (the shipped `config.yaml`) they call `save_email`, which
  stores the whole email with the owner's verdict as a triage example (`human_inbox.py:61-70`),
  and on a respond or an edit they start `multi_reflection_graph` through the LangGraph SDK.
- `multi_reflection_graph`. `determine_what_to_update`, an LLM agent, picks the preferences to
  change, and `update_general`, an LLM agent in `general_reflection_graph`, rewrites them in
  the store. The trajectory it reads holds the email.
- `mark_as_read_node`, `send_email_node`, `send_cal_invite_node`, plain code calling Gmail.

No upstream issue names a cross-sender path. The two paths seen in code are A's email reaching
B's triage as a few-shot example, which needs only that the owner handled A's email at all,
and A's email reaching B's draft through the reflected preferences, which needs the owner to
respond or edit (`notes/subject-search.md`, EAIA).

Runs are one email each, from A and then B, in threads of their own, on one store. Every LLM
choice (triage label, draft tool, which preferences to reflect) and every owner answer is
enumerated. The owner's edits and responses are fixed text, so no path carries text through
the owner.

Stubs. `ChatOpenAI` and `ChatAnthropic` are marker LLMs. A tool call depends on the step, so
each call builds a fresh `marker_llm`. `eaia.gmail` is replaced by a module of offline
functions, the SDK client by one that runs the reflection graph inline in the calling node, so
its tasks are nested in the run, and the store's index embeds with `DeterministicFakeEmbedding`.
"""

from __future__ import annotations

import asyncio
import functools
import sys
import traceback
import types
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from drivers import emit_json, on_path, options, report, repo
import lgtrace
from lgtrace import Run, Script, Subject, make_markers, marker_llm, router_scripts

NAME = "executive_ai_assistant"
REPO = "executive-ai-assistant"
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"A"})
MAX_RESUMES = 10
EMBED_DIMS = 16

TOOLS: Mapping[str, dict[str, Any]] = {
  "ResponseEmailDraft": {"content": "Reply {markers}", "new_recipients": []},
  "Question": {"content": "Should I answer? {markers}"},
  "MeetingAssistant": {"call": True},
  "SendCalendarInvite": {"emails": ["sender@example.com"], "title": "Sync {markers}",
                         "start_time": "2025-07-01T14:00:00",
                         "end_time": "2025-07-01T14:30:00"},
}
EDITS: Mapping[str, dict[str, Any]] = {
  "ResponseEmailDraft": {"content": "Edited by the owner.", "new_recipients": []},
  "SendCalendarInvite": {"emails": ["sender@example.com"], "title": "Owner's title",
                         "start_time": "2025-07-01T15:00:00",
                         "end_time": "2025-07-01T15:30:00"},
}
ANSWERS: Mapping[str, tuple[str, ...]] = {  # what Agent Inbox allows per interrupt
  "Notify": ("ignore", "response"),
  "Question": ("ignore", "response"),
  "ResponseEmailDraft": ("accept", "edit", "ignore", "response"),
  "SendCalendarInvite": ("accept", "edit", "ignore", "response"),
}
REFLECT = {"none": [], "all": ["tone", "background", "email", "calendar"]}
CHOICES: Mapping[str, tuple[str, ...]] = {
  "triage": ("no", "email", "notify", "question"),
  "notify_human": ANSWERS["Notify"],
  "tool": tuple(TOOLS),
  "tool_human": ANSWERS["ResponseEmailDraft"],
  "reflect": tuple(REFLECT),
}


def relevant(s: Mapping[str, str]) -> tuple[tuple[str, str], ...] | None:
  """The choices a script exercises, or None for an answer Agent Inbox does not offer."""
  keys = ["triage"]
  drafts = s["triage"] in ("email", "question")
  if s["triage"] == "notify":
    keys.append("notify_human")
    drafts = s["notify_human"] == "response"
  if drafts:
    keys.append("tool")
    if s["tool"] in ANSWERS:
      if s["tool_human"] not in ANSWERS[s["tool"]]:
        return None
      keys.append("tool_human")
  reflects = ((s["triage"] == "notify" and s["notify_human"] == "response")
              or (drafts and s["tool"] in ANSWERS and s["tool_human"] in ("edit", "response")))
  if reflects:
    keys.append("reflect")
  return tuple((k, s[k]) for k in keys)


def scripts() -> tuple[dict[str, str], ...]:
  keyed = {key: s for s in router_scripts(CHOICES) if (key := relevant(s)) is not None}
  return tuple(dict(key) for key in keyed)


# ---------------------------------------------------------------------------------------------
# Fake models


@dataclass
class Current:
  markers: Mapping[str, str]
  script: Script


CURRENT = Current({}, {})


def ai_turns(messages: Any) -> int:
  from langchain_core.messages import AIMessage
  return sum(isinstance(m, AIMessage) for m in messages or [])


class FakeChat:
  """Stands in for `ChatOpenAI(...)` and `ChatAnthropic(...)`. Each call builds a fresh
  `marker_llm` from the script being traced."""

  def __init__(self, *args: Any, **kwargs: Any) -> None:
    pass

  @staticmethod
  def llm(script: Mapping[str, Any]) -> Any:
    return marker_llm(CURRENT.markers, script)

  def structured_script(self) -> dict[str, Any]:
    s = CURRENT.script
    return {"RespondTo": {"response": s["triage"]},
            "MemoryToUpdate": {"memory_types_to_update": REFLECT[s.get("reflect", "none")]},
            "GeneralResponse": {"update_prompt": True, "logic": "",
                                "new_prompt": "Preferences {markers}"}}

  def with_structured_output(self, schema: Any, **kwargs: Any) -> Any:
    """The structured model, taking and dropping the `tool_choice` that `.bind` adds."""
    from langchain_core.runnables import RunnableLambda
    inner = self.llm(self.structured_script()).with_structured_output(schema)
    return RunnableLambda(lambda value, **bound: inner.invoke(value))

  def bind_tools(self, tools: Any, **kwargs: Any) -> Any:
    from langchain_core.runnables import RunnableLambda
    names = {getattr(t, "__name__", getattr(t, "name", None)) for t in tools}

    def call(messages: Any) -> Any:
      if "Ignore" not in names and "ResponseEmailDraft" not in names:
        return self.llm({"text": "Free at 3pm. {markers}"}).invoke(messages)  # meeting agent
      turn = ai_turns(messages)
      chosen = CURRENT.script["tool"] if turn == 0 else "Ignore"
      args = TOOLS.get(chosen, {"ignore": True})
      return self.llm({"tool_calls": [{"name": chosen, "args": args}]}).invoke(messages)
    return RunnableLambda(call)

  def invoke(self, messages: Any, *args: Any, **kwargs: Any) -> Any:
    return self.llm({"text": "Free at 3pm. {markers}"}).invoke(messages)


# ---------------------------------------------------------------------------------------------
# Offline Gmail, SDK client and store


def gmail_module() -> types.ModuleType:
  from langchain_core.tools import tool

  @tool
  def get_events_for_days(date_strs: list[str]) -> str:
    """Retrieves events for a list of days."""
    return "No events."

  mod = types.ModuleType("eaia.gmail")
  mod.__dict__.update(
    send_email=lambda *a, **k: None, mark_as_read=lambda *a, **k: None,
    send_calendar_invite=lambda *a, **k: True, get_events_for_days=get_events_for_days,
    fetch_group_emails=lambda *a, **k: iter(()))
  return mod


@dataclass
class InlineRuns:
  """`LGC.runs`. `create` runs the reflection graph inline, in the calling node's task."""
  graphs: Mapping[str, Any]

  async def create(self, thread_id: Any, assistant_id: str, input: Any = None,
                   **kwargs: Any) -> dict[str, Any]:
    await self.graphs[assistant_id].ainvoke(input)
    return {"run_id": "inline"}


def store_factory() -> Any:
  from langchain_core.embeddings import DeterministicFakeEmbedding
  from langgraph.store.memory import InMemoryStore
  return InMemoryStore(index={"embed": DeterministicFakeEmbedding(size=EMBED_DIMS),
                              "dims": EMBED_DIMS})


@functools.cache
def subject_modules() -> types.SimpleNamespace:
  on_path(repo(REPO))
  sys.modules["eaia.gmail"] = gmail_module()
  import eaia.main.draft_response as draft
  import eaia.main.find_meeting_time as meeting
  import eaia.main.graph as graph
  import eaia.main.human_inbox as inbox
  import eaia.main.rewrite as rewrite
  import eaia.main.triage as triage
  import eaia.reflection_graphs as reflection
  for mod in (draft, meeting, rewrite, triage, reflection):
    mod.ChatOpenAI = FakeChat
  reflection.ChatAnthropic = FakeChat
  return types.SimpleNamespace(graph=graph, inbox=inbox, reflection=reflection,
                               general=reflection.general_reflection_graph,
                               multi=reflection.multi_reflection_graph)


# ---------------------------------------------------------------------------------------------
# The owner and the runs


def owner_answer(script: Script, request: Mapping[str, Any]) -> list[dict[str, Any]]:
  action = request["action_request"]["action"]
  kind = script["notify_human" if action == "Notify" else "tool_human"]
  args = {"accept": None, "ignore": None, "response": "Keep it short.",
          "edit": {"args": EDITS.get(action, {})}}[kind]
  return [{"type": kind, "args": args}]


CRASHES: list[str] = []


def crash_site(e: BaseException) -> str:
  frame = traceback.extract_tb(e.__traceback__)[-1]
  where = f"{Path(frame.filename).parent.name}/{Path(frame.filename).name}:{frame.lineno}"
  return f"{type(e).__name__} at {where}: {e}"


@dataclass(frozen=True)
class OwnerDriven:
  """A compiled graph whose `stream` drives `astream` and answers every interrupt like the
  scripted owner. An exception of the app ends the run and is kept in `CRASHES`."""
  graph: Any
  answer: Callable[[Mapping[str, Any]], Any]

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    from langgraph.types import Command

    async def collect() -> list[Any]:
      events: list[Any] = []  # filled as they come, so a crash keeps the events before it
      try:
        async for ev in self.graph.astream(inp, config, **kwargs):
          events.append(ev)
        for _ in range(MAX_RESUMES):
          state = await self.graph.aget_state(config)
          pending = [i for t in state.tasks for i in t.interrupts]
          if not pending:
            return events
          resume = Command(resume=self.answer(pending[0].value[0]))
          async for ev in self.graph.astream(resume, config, **kwargs):
            events.append(ev)
        raise RuntimeError(f"more than {MAX_RESUMES} interrupts in one run")
      except Exception as e:  # noqa: BLE001, the app's own crash ends the run
        CRASHES.append(crash_site(e))
      return events
    yield from asyncio.run(collect())


def build(markers: Mapping[str, str]) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    from langgraph.checkpoint.memory import InMemorySaver
    mods = subject_modules()
    CURRENT.markers, CURRENT.script = markers, script
    general = lgtrace.instrument_compiled(mods.general, store=store)
    mods.reflection.general_reflection_graph = general  # `call_reflection` reads the global
    multi = lgtrace.instrument_compiled(mods.multi, store=store)
    mods.inbox.LGC = types.SimpleNamespace(runs=InlineRuns({"multi_reflection_graph": multi}))
    graph = lgtrace.instrument(mods.graph.graph_builder).compile(
      store=store, checkpointer=InMemorySaver())
    return OwnerDriven(graph, functools.partial(owner_answer, script))
  return go


def email(principal: str, marker: str) -> dict[str, Any]:
  return {"email": {"id": f"m-{principal}", "thread_id": f"t-{principal}",
                    "from_email": f"sender{principal}@example.com",
                    "to_email": "harrison@langchain.dev",
                    "subject": f"Hello from {principal}", "send_time": "2025-07-01T09:00:00",
                    "page_content": f"Hi Harrison, this is sender {principal}. {marker}"}}


def subject() -> Subject:
  markers = make_markers(PRINCIPALS)
  runs = tuple(Run(email(p, markers[p]), p, {"configurable": {"thread_id": f"thread-{p}"},
                                             "recursion_limit": 50})
               for p in PRINCIPALS)
  return Subject(build(markers), runs, markers, ATTACKERS, scripts(), store=store_factory)


def main() -> None:
  opts = options()
  CRASHES.clear()
  summary = report(NAME, opts.narrow(subject()), opts.write)
  summary["crashes"] = {c: CRASHES.count(c) for c in sorted(set(CRASHES))}
  print("".join(f"app crash in {n} runs: {c}\n" for c, n in summary["crashes"].items()), end="")
  emit_json([summary])


if __name__ == "__main__":
  main()
