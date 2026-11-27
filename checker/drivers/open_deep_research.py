"""lgtrace adapter for langchain-ai/open_deep_research `1b7d2e8`, a precision check.

Open Deep Research writes a research report on a question. It is deployed on the LangGraph
platform behind `src/security/auth.py`, which tags each thread with its owner, so many users
share one server, one store and one process. Actors
- the user, a human, who asks a question in a thread of their own and may answer a clarifying
  question in a second turn.
- `clarify_with_user`, an LLM agent that asks a clarifying question or confirms the scope.
- `write_research_brief`, an LLM agent that turns the conversation into a research brief.
- `research_supervisor`, a subgraph. `supervisor` is an LLM agent that plans and delegates with
  tool calls, and `supervisor_tools`, plain code, runs them. A `ConductResearch` call starts the
  researcher subgraph from inside `supervisor_tools`.
- the researcher subgraph. `researcher` is an LLM agent with search and MCP tools,
  `researcher_tools` is plain code that runs them (the Tavily tool calls a summarizer LLM), and
  `compress_research` is an LLM agent that condenses the findings.
- `final_report_generation`, an LLM agent that writes the report.

State shared across users
- The store. `fetch_tokens` (`utils.py:352`) caches each user's MCP access token under
  `(owner, "tokens")`, where `owner` is the thread metadata the auth handler sets.
- Module globals. `configurable_model` (`deep_researcher.py:60`) is one configurable chat model
  for every user, and `tavily_search.metadata` is updated in place on every call. Neither holds
  user text.

No upstream issue reports a cross-user leak, so the expected result is no finding. Runs are
user A's question, user B's question and A's second turn in A's thread, on one server. A's
second turn shows that A's own thread state and token still reach A. Every LLM choice is
enumerated: the clarifier asks or proceeds, the supervisor delegates, thinks then delegates, or
finishes at once, and the researcher searches, calls the MCP tool or answers without tools.

Stubs. `configurable_model` and the summarizer's `init_chat_model` become marker LLMs. A tool
call depends on the step, so each call builds a fresh `marker_llm` whose script is chosen from
the number of AI messages in its input. Tavily search returns one fixed page. The MCP token
exchange returns a token derived from the user's Supabase token, and the MCP client serves one
tool, `read_doc`, that returns a fixed document.
"""

from __future__ import annotations

import asyncio
import functools
import sys
import types
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from typing import Any

from drivers import emit_json, on_path, options, report, repo, run_order, turns
from lgtrace import Run, Script, Subject, instrument, marker_llm, make_markers, router_scripts

NAME = "open_deep_research"
REPO = "open_deep_research"
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"A"})
MCP_URL = "http://mcp.invalid"
PAGE = "Deep research agents plan, search and write reports."
DOC = "Internal document about the research topic."

SUPERVISOR: Mapping[str, tuple[list[dict[str, Any]], ...]] = {
  "delegate": ([{"name": "ConductResearch", "args": {"research_topic": "Topic {markers}"}}],
               [{"name": "ResearchComplete", "args": {}}]),
  "think": ([{"name": "think_tool", "args": {"reflection": "Plan {markers}"}}],
            [{"name": "ConductResearch", "args": {"research_topic": "Topic {markers}"}}],
            [{"name": "ResearchComplete", "args": {}}]),
  "finish": ([{"name": "ResearchComplete", "args": {}}],),
}
RESEARCHER: Mapping[str, tuple[list[dict[str, Any]], ...]] = {
  "search": ([{"name": "tavily_search", "args": {"queries": ["Query {markers}"]}}],
             [{"name": "ResearchComplete", "args": {}}]),
  "mcp": ([{"name": "read_doc", "args": {"query": "Query {markers}"}}],
          [{"name": "ResearchComplete", "args": {}}]),
  "none": ([],),
}
CHOICES: Mapping[str, tuple[str, ...]] = {"clarify": ("ask", "proceed"),
                                          "supervisor": tuple(SUPERVISOR),
                                          "researcher": tuple(RESEARCHER)}


def scripts() -> tuple[dict[str, str], ...]:
  """Every combination, dropping the researcher choice when the supervisor never delegates."""
  def relevant(s: Mapping[str, str]) -> tuple[tuple[str, str], ...]:
    return tuple((k, v) for k, v in s.items()
                 if not (k == "researcher" and s["supervisor"] == "finish"))
  return tuple(dict(k) for k in dict.fromkeys(map(relevant, router_scripts(CHOICES))))


# ---------------------------------------------------------------------------------------------
# Fake models


def ai_turns(messages: Any) -> int:
  """The number of AI messages in a model input, which says how far its tool loop is."""
  from langchain_core.messages import AIMessage
  return sum(isinstance(m, AIMessage) for m in messages or [])


def has_ai_turn(messages: Any) -> bool:
  """Whether a prompt built with `get_buffer_string` already holds an AI turn."""
  return any("\nAI: " in f"\n{getattr(m, 'content', '')}" for m in messages or [])


@dataclass(frozen=True)
class FakeModel:
  """Stands in for `configurable_model`, building a fresh `marker_llm` for every call."""
  markers: Mapping[str, str]
  script: Script

  def llm(self, script: Mapping[str, Any]) -> Any:
    return marker_llm(self.markers, script)

  def with_structured_output(self, schema: Any, **kwargs: Any) -> Any:
    from langchain_core.runnables import RunnableLambda

    def call(messages: Any) -> Any:
      ask = self.script["clarify"] == "ask" and not has_ai_turn(messages)
      clarify = {"need_clarification": ask, "question": "Which scope? {markers}",
                 "verification": "Starting research on {markers}"}
      return self.llm({"ClarifyWithUser": clarify}).with_structured_output(schema).invoke(
        messages)
    return RunnableLambda(call)

  def bind_tools(self, tools: Any, **kwargs: Any) -> Any:
    from langchain_core.runnables import RunnableLambda
    names = {getattr(t, "__name__", None) or getattr(t, "name", None) for t in tools}
    steps = (SUPERVISOR[self.script["supervisor"]] if "ConductResearch" in names
             else RESEARCHER[self.script.get("researcher", "none")])

    def call(messages: Any) -> Any:
      step = steps[min(ai_turns(messages), len(steps) - 1)]
      return self.llm({"tool_calls": step, "text": "Notes {markers}"}).invoke(messages)
    return RunnableLambda(call)

  def with_config(self, *args: Any, **kwargs: Any) -> Any:
    return self.llm({"text": "Report {markers}"})


# ---------------------------------------------------------------------------------------------
# Offline tools


async def tavily_stub(queries: list[str], **kwargs: Any) -> list[dict[str, Any]]:
  return [{"query": q, "results": [{"url": "https://example.com/page", "title": "Page",
                                    "content": PAGE, "raw_content": PAGE}]} for q in queries]


async def token_exchange_stub(supabase_token: str, base_mcp_url: str) -> dict[str, Any]:
  return {"access_token": f"mcp-{supabase_token}", "expires_in": 3600}


class MCPClientStub:
  """`MultiServerMCPClient` serving one tool, `read_doc`."""

  def __init__(self, connections: Mapping[str, Any], **kwargs: Any) -> None:
    self.connections = connections

  async def get_tools(self) -> list[Any]:
    from langchain_core.tools import StructuredTool

    async def read_doc(query: str) -> str:
      return DOC
    return [StructuredTool.from_function(coroutine=read_doc, name="read_doc",
                                         description="Read an internal document.")]


@functools.cache
def subject_modules() -> types.SimpleNamespace:
  """The real modules, imported with the stubs in place."""
  on_path(repo(REPO) / "src")
  import open_deep_research.deep_researcher as dr
  import open_deep_research.utils as utils
  utils.tavily_search_async = tavily_stub
  utils.get_mcp_access_token = token_exchange_stub
  utils.MultiServerMCPClient = MCPClientStub
  return types.SimpleNamespace(dr=dr, utils=utils)


# ---------------------------------------------------------------------------------------------
# Graph and runs


@dataclass(frozen=True)
class AsyncGraph:
  """A compiled graph whose `stream` drives `astream`, since every node is a coroutine."""
  graph: Any

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    async def collect() -> list[Any]:
      return [ev async for ev in self.graph.astream(inp, config, **kwargs)]
    yield from asyncio.run(collect())


def build(markers: Mapping[str, str]) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    from langgraph.checkpoint.memory import InMemorySaver
    mods = subject_modules()
    model = FakeModel(markers, script)
    mods.dr.configurable_model = model
    mods.utils.init_chat_model = lambda *a, **k: model.llm({})
    mods.dr.researcher_subgraph = instrument(mods.dr.researcher_builder).compile()
    graph = instrument(mods.dr.deep_researcher_builder).compile(
      store=store, checkpointer=InMemorySaver())
    return AsyncGraph(graph)
  return go


def message(principal: str, turn: int, marker: str) -> dict[str, Any]:
  text = (f"I am user {principal}. Research this for me: {marker}" if turn == 0
          else f"User {principal} here, the scope is {marker}")
  return {"messages": [{"role": "user", "content": text}]}


def config(principal: str) -> dict[str, Any]:
  return {"configurable": {"thread_id": f"thread-{principal}",
                           "x-supabase-access-token": f"sb-{principal}",
                           "mcp_config": {"url": MCP_URL, "tools": ["read_doc"],
                                          "auth_required": True}},
          "metadata": {"owner": principal}, "recursion_limit": 100}


def subject() -> Subject:
  markers = make_markers(PRINCIPALS)
  runs = tuple(Run(message(p, turn, markers[p]), p, config(p)) for p, turn in turns(run_order(PRINCIPALS, ATTACKERS)))
  return Subject(build(markers), runs, markers, ATTACKERS, scripts())


def main() -> None:
  opts = options()
  emit_json([report(NAME, opts.narrow(subject()), opts.write)])


if __name__ == "__main__":
  main()
