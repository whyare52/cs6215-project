"""lgtrace adapter for kaymen99/langgraph-email-automation `9ea0f54`.

One graph run answers a batch of customer emails for a company. Actors
- `load_inbox_emails`, plain code that fetches the unanswered emails from Gmail.
- `categorize_email`, an LLM agent that labels the last email in the batch.
- `construct_rag_queries` and `retrieve_from_rag`, LLM agents that ask the product docs
  (a vector store) about a product enquiry.
- `email_writer`, an LLM agent that drafts the reply, with the drafts and feedback so far.
- `email_proofreader`, an LLM agent that decides whether the draft can be sent.
- `send_email`, plain code that stores the draft in Gmail. `must_rewrite`, plain code on the
  proofreader's edge, sends, rewrites or stops after three trials, then moves to the next email.

The run batches customers A (the attacker) and B, so `principal_of` names the customer of each
task from the email it handles. Every LLM choice (each customer's category and each proofreader
verdict sequence) is enumerated by `router_scripts`.

Stubs. `langchain_groq`, `langchain_google_genai` and `langchain_chroma` are replaced by modules
whose chat models are the script's `marker_llm` and whose retriever returns one fixed product
document, so the real `src/agents.py` chains run offline. `src.tools.GmailTools` is replaced by
an inbox holding the batch, which records drafts instead of calling Gmail.

`fixed_subject()` fixes the lost clear in `must_rewrite` (`src/nodes.py:127,132`). A plain-code
node `clear_drafts` runs before every `categorize_email` and returns a `RemoveMessage` for each
writer message. It still serves the previous customer, since `current_email` is not yet
replaced, so its read of that customer's drafts stays within the customer. A clear inside
`categorize_email` would read the drafts while serving the next customer, which read tracking
reports as a flow.
"""

from __future__ import annotations

import contextlib
import functools
import logging
import sys
import traceback
import types
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from drivers import emit_json, on_path, options, report, repo
from lgtrace import (Run, Script, Subject, instrument, make_markers, marker_llm, router_scripts,
                     seq)

NAME = "kaymen99"
REPO = "langgraph-email-automation"
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"A"})
CATEGORIES = ("product_enquiry", "customer_complaint", "customer_feedback", "unrelated")
VERDICTS: Mapping[str, tuple[bool, ...]] = {
  "send": (True,), "rewrite": (False, True), "stop": (False, False, False)}
PRODUCT_DOC = "The Pro plan costs 20 dollars a month and includes priority support."


def choices() -> dict[str, tuple[str, ...]]:
  """Per customer, in processing order, a category and a proofreader verdict sequence."""
  return {k: v for p in PRINCIPALS
          for k, v in ((f"category_{p}", CATEGORIES), (f"proof_{p}", tuple(VERDICTS)))}


def scripts() -> tuple[dict[str, str], ...]:
  """Every combination, dropping proofreader choices for an unrelated email, which skips it."""
  def relevant(s: Mapping[str, str]) -> tuple[tuple[str, str], ...]:
    return tuple((k, v) for k, v in s.items()
                 if not (k.startswith("proof_") and s[f"category_{k[6:]}"] == "unrelated"))
  return tuple(dict(key) for key in dict.fromkeys(map(relevant, router_scripts(choices()))))


def llm_script(script: Script) -> dict[str, Any]:
  verdicts = [v for p in PRINCIPALS if script[f"category_{p}"] != "unrelated"
              for v in VERDICTS[script[f"proof_{p}"]]]
  return {
    "CategorizeEmailOutput": seq(*({"category": script[f"category_{p}"]} for p in PRINCIPALS)),
    "ProofReaderOutput": seq(*({"send": v} for v in verdicts or [True])),
    "RAGQueriesOutput": {"queries": ["Which plan fits? {markers}"]},
  }


# ---------------------------------------------------------------------------------------------
# Stubs


@dataclass
class Inbox:
  """The Gmail stub. `fetch_unanswered_emails` returns the batch, and drafts are recorded."""
  emails: Sequence[Mapping[str, str]] = ()
  drafts: list[tuple[str, str]] = field(default_factory=list)

  def fetch_unanswered_emails(self, max_results: int = 50) -> list[dict[str, str]]:
    return [dict(e) for e in self.emails]

  def create_draft_reply(self, initial_email: Any, reply_text: str) -> None:
    self.drafts.append((initial_email.id, reply_text))

  def send_reply(self, initial_email: Any, reply_text: str) -> None:
    self.drafts.append((initial_email.id, reply_text))


@dataclass
class Current:
  """What the stub modules hand out while `Workflow()` builds the chains for one script."""
  llm: Any = None
  inbox: Inbox = field(default_factory=Inbox)


CURRENT = Current()


def retriever() -> Any:
  from langchain_core.documents import Document
  from langchain_core.runnables import RunnableLambda
  return RunnableLambda(lambda query: [Document(page_content=PRODUCT_DOC)])


def stub_modules() -> dict[str, types.ModuleType]:
  def module(name: str, **attrs: Any) -> types.ModuleType:
    mod = types.ModuleType(name)
    mod.__dict__.update(attrs)
    return mod
  chat = lambda *a, **k: CURRENT.llm  # noqa: E731
  vectorstore = types.SimpleNamespace(as_retriever=lambda **k: retriever())
  return {
    "langchain_groq": module("langchain_groq", ChatGroq=chat),
    "langchain_google_genai": module("langchain_google_genai", ChatGoogleGenerativeAI=chat,
                                     GoogleGenerativeAIEmbeddings=lambda *a, **k: None),
    "langchain_chroma": module("langchain_chroma", Chroma=lambda *a, **k: vectorstore),
    "src.tools.GmailTools": module("src.tools.GmailTools", GmailToolsClass=lambda: CURRENT.inbox),
  }


@functools.cache
def subject_modules() -> types.SimpleNamespace:
  """The real `src.graph` and `src.nodes`, imported with the stubs in place."""
  on_path(repo(REPO))
  sys.modules.update(stub_modules())
  if "colorama" not in sys.modules:
    try:
      import colorama  # noqa: F401
    except ImportError:
      sys.modules["colorama"] = types.ModuleType("colorama")
      sys.modules["colorama"].__dict__.update(
        Fore=types.SimpleNamespace(YELLOW="", RED="", GREEN="", MAGENTA="", CYAN=""),
        Style=types.SimpleNamespace(RESET_ALL=""))
  import src.graph
  import src.nodes
  return types.SimpleNamespace(graph=src.graph, nodes=src.nodes)


# ---------------------------------------------------------------------------------------------
# The fix


CLEAR = "clear_drafts"


def clear_drafts(state: Mapping[str, Any]) -> dict[str, Any]:
  """Remove every writer message of the email just finished."""
  from langchain_core.messages import RemoveMessage
  old = [m.id for m in state.get("writer_messages", []) if getattr(m, "id", None)]
  return {"writer_messages": [RemoveMessage(id=i) for i in old]}


@contextlib.contextmanager
def quiet_langgraph() -> Iterator[None]:
  """Silence LangGraph's warning about changing a builder that `Workflow` already compiled."""
  log = logging.getLogger("langgraph.graph")
  level = log.level
  log.setLevel(logging.ERROR)
  try:
    yield
  finally:
    log.setLevel(level)


def with_clear(builder: Any) -> Any:
  """`builder` with `clear_drafts` on every edge into `categorize_email`, changed in place."""
  with quiet_langgraph():
    builder.add_node(CLEAR, clear_drafts)
    builder.add_edge(CLEAR, "categorize_email")
  for branches in builder.branches.values():
    for name, branch in list(branches.items()):
      ends = {k: CLEAR if v == "categorize_email" else v for k, v in (branch.ends or {}).items()}
      branches[name] = branch._replace(ends=ends)
  return builder


# ---------------------------------------------------------------------------------------------
# Graph, runs and principals


@dataclass(frozen=True)
class CrashTolerant:
  """A compiled graph whose `stream` ends at an app exception, keeping the events before it."""
  graph: Any
  crashes: list[str]

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    try:
      yield from self.graph.stream(inp, config, **kwargs)
    except Exception as e:  # noqa: BLE001, the app's own crash ends the run
      frame = traceback.extract_tb(e.__traceback__)[-1]
      where = f"{Path(frame.filename).parent.name}/{Path(frame.filename).name}:{frame.lineno}"
      self.crashes.append(f"{type(e).__name__} at {where}: {e}")


CRASHES: list[str] = []


def build(markers: Mapping[str, str], inbox: Sequence[Mapping[str, str]],
          fixed: bool) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    mods = subject_modules()
    CURRENT.llm, CURRENT.inbox = marker_llm(markers, llm_script(script)), Inbox(inbox)
    builder = mods.graph.Workflow().app.builder  # a fresh builder per call
    graph = instrument(with_clear(builder) if fixed else builder).compile(store=store)
    return CrashTolerant(graph, CRASHES)
  return go


def email(principal: str, marker: str) -> dict[str, str]:
  return {"id": f"m-{principal}", "threadId": f"t-{principal}", "messageId": f"<{principal}@x>",
          "references": "", "sender": f"customer{principal}@example.com",
          "subject": f"Question from {principal}",
          "body": f"Hello, this is customer {principal}. {marker}"}


def initial_state(inbox: Sequence[Mapping[str, str]]) -> dict[str, Any]:
  """`main.py`'s initial state, with the batch also in `emails`.

  `load_new_emails` overwrites `emails` with the same batch from the stub. Putting it in the run
  input makes the email bodies raw input for lgtrace, so a task reading the whole batch does not
  link customers.
  """
  blank = dict.fromkeys(("id", "threadId", "messageId", "references", "sender", "subject",
                         "body"), "")
  return {"emails": [dict(e) for e in inbox], "current_email": blank, "email_category": "",
          "generated_email": "", "rag_queries": [], "retrieved_documents": "",
          "writer_messages": [], "sendable": False, "trials": 0}


def owner_of(markers: Mapping[str, str]) -> Callable[[Any], str | None]:
  def owner(email_value: Any) -> str | None:
    body = (email_value.get("body") if isinstance(email_value, Mapping)
            else getattr(email_value, "body", "")) or ""
    found = [p for p, m in markers.items() if m in body]
    return found[0] if len(found) == 1 else None
  return owner


def principal_of(markers: Mapping[str, str]) -> Callable[[str, Any], str | None]:
  """The customer whose email a task handles. `categorize_email` picks up the last email.

  Tasks after an email is done, such as `is_email_inbox_empty`, belong to that email's customer.
  """
  owner = owner_of(markers)

  def who(node: str, state: Any) -> str | None:
    if not isinstance(state, Mapping) or node == "load_inbox_emails":
      return None
    if node == "categorize_email" and state.get("emails"):
      return owner(state["emails"][-1])
    return owner(state.get("current_email"))  # an empty batch crashes on the last customer
  return who


def make_subject(fixed: bool) -> Subject:
  markers = make_markers(PRINCIPALS)
  inbox = [email(p, markers[p]) for p in reversed(PRINCIPALS)]  # the last email goes first
  run = Run(initial_state(inbox), config={"recursion_limit": 100})
  return Subject(build(markers, inbox, fixed), (run,), markers, ATTACKERS, scripts(),
                 principal_of=principal_of(markers))


def subject() -> Subject:
  return make_subject(fixed=False)


def fixed_subject() -> Subject:
  return make_subject(fixed=True)


def main() -> None:
  opts, summaries = options(), []
  for name, make in ((NAME, subject), (f"{NAME}-fixed", fixed_subject)):
    CRASHES.clear()
    summary = report(name, opts.narrow(make()), opts.write)
    summary["crashes"] = {c: CRASHES.count(c) for c in sorted(set(CRASHES))}
    print("".join(f"app crash in {n} of {summary['scripts']} scripts: {c}\n"
                  for c, n in summary["crashes"].items()), end="")
    summaries.append(summary)
  emit_json(summaries)


if __name__ == "__main__":
  main()
