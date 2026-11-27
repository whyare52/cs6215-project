import asyncio
import dataclasses
import importlib.util
import json
import os
import sys
import tempfile
import threading
import unittest
from pathlib import Path
from typing import Annotated, Literal, TypedDict

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from irspec import reach  # noqa: E402
from lgtrace import (  # noqa: E402
  RESOURCES, Access, ExternalTask, FileRecorder, Handoff, LLMCall, ReadOp, Rules, Run, Stamped,
  StoreOp, Subject, Trace, acting, cross_reads, current_task, emit, extract, findings, flows,
  instrument, marker_llm, recorded, recording_store, router_scripts, shared_reads, spec_dict,
  task_id_of, to_spec, trace_from_events, trace_subject, unexplained)

HAS_LANGGRAPH = importlib.util.find_spec("langgraph") is not None
MARKERS = {"A": "MKAZ", "B": "MKBZ"}


def acc(task, principal, channel, mode, value, node="n", run="0", thread="", seq=0):
  return Access(run, task, node, principal, channel, mode, value, thread, seq)


MAIL = {"A": "mail MKAZ", "B": "mail MKBZ"}


def trace(*accesses, inputs=None):
  return Trace(MARKERS, inputs or {"0": {"email": list(MAIL.values())}}, tuple(accesses))


def start(task, principal, node="n", run="0"):
  """A task of `principal` reading its own raw input, which puts it on `in#principal`."""
  return acc(task, principal, "email", "read", MAIL[principal], node=node, run=run)


def victims(t, attackers=("A",), rules=Rules()):
  return set(findings(to_spec(t, attackers, rules)))


def boards_on(path):
  return [step.split(" via board ")[1] for step in path if " via board " in step]


class CoreTests(unittest.TestCase):
  def test_state_key_flow_to_other_principal(self):
    t = trace(start("t1", "A", node="writer"),
              acc("t1", "A", "msgs", "write", ["draft MKAZ"], node="writer"),
              acc("t2", "B", "msgs", "read", ["draft MKAZ"], node="writer"))
    self.assertEqual(victims(t), {"writer@B"})
    path = findings(to_spec(t, ["A"]))["writer@B"]
    self.assertEqual(boards_on(path), ["in#A", "msgs#A<-writer@A"])

  def test_store_namespace_flow_to_other_principal(self):
    t = trace(start("t1", "A", node="memory"),
              acc("t1", "A", "store:prefs", "write", {"rules": "x MKAZ"}, node="memory"),
              acc("t2", "B", "store:prefs", "read", {"rules": "x MKAZ"}, node="triage"))
    self.assertEqual(victims(t), {"triage@B"})

  def test_cleared_channel_gives_no_finding(self):
    t = trace(start("t1", "A"), acc("t1", "A", "msgs", "write", ["draft MKAZ"]),
              acc("t2", "B", "msgs", "read", []))
    self.assertEqual(victims(t), set())
    self.assertEqual(flows(t), frozenset())

  def test_same_principal_flow_gives_no_finding(self):
    t = trace(start("t1", "A", node="w"), start("t3", "B", node="r"),
              acc("t1", "A", "msgs", "write", ["MKAZ"], node="w"),
              acc("t2", "A", "msgs", "read", ["MKAZ"], node="r"),
              acc("t3", "B", "msgs", "read", ["MKBZ"], node="r"))
    self.assertEqual(victims(t), set())
    self.assertEqual(reach(to_spec(t, ["A"])), {"input@A", "w@A", "r@A"})

  def test_raw_input_of_another_principal_carries_no_flow(self):
    inbox = ["hi MKAZ", "yo MKBZ"]
    t = trace(acc("t1", "A", "inbox", "read", inbox, node="load"),
              acc("t2", "B", "inbox", "read", inbox, node="load"),
              inputs={"0": {"inbox": inbox}})
    spec = spec_dict(t, ["A"])
    self.assertEqual(spec["boards"]["in#A"], {"readers": ["load@A"], "writers": ["input@A"]})
    self.assertEqual(spec["boards"]["in#B"], {"readers": ["load@B"], "writers": ["input@B"]})
    self.assertEqual(victims(t), set())

  def test_batched_inbox_needs_raw_rule(self):
    """kaymen99's shape. The first customer's task reads the whole inbox key, with the second
    customer's email in it, though it only handles its own."""
    inbox = ["hi MKAZ", "yo MKBZ"]
    t = trace(acc("t1", "A", "inbox", "read", inbox, node="categorize"),
              acc("t2", "B", "inbox", "read", inbox[1:], node="categorize"),
              inputs={"0": {"inbox": inbox}})
    self.assertEqual(victims(t, ["B"]), set())
    self.assertEqual(victims(t, ["B"], Rules(raw_rule=False)), {"categorize@A"})

  def test_relayed_raw_input_is_credited_to_its_input(self):
    """kaymen99's `skip_unrelated_email@A` returns the state, B's email included. B reading its
    own email must not be reached from A through that write."""
    inbox = ["hi MKAZ", "yo MKBZ"]
    t = trace(acc("t1", "A", "inbox", "read", inbox, node="skip", seq=1),
              acc("t1", "A", "inbox", "write", inbox[1:], node="skip", seq=2),
              acc("t2", "B", "inbox", "read", inbox[1:], node="categorize", seq=3),
              inputs={"0": {"inbox": inbox}})
    self.assertEqual(victims(t), set())
    self.assertEqual(victims(t, rules=Rules(raw_from_input=False)), {"categorize@B"})

  def test_reader_links_only_to_the_writer_of_what_it_saw(self):
    """B's task rewrites A's text after A's reader read it, as kaymen99's proofreader rewrites
    the drafts list. Split boards keep A's earlier reader out of B's reach."""
    t = trace(start("t1", "A", node="writer"),
              acc("t1", "A", "msgs", "write", ["draft MKAZ"], node="writer", seq=2),
              acc("t2", "A", "msgs", "read", ["draft MKAZ"], node="proof", seq=3),
              start("t3", "B", node="proof"),
              acc("t3", "B", "msgs", "write", ["draft MKAZ", "fb MKBZ"], node="proof", seq=5),
              acc("t4", "B", "msgs", "read", ["draft MKAZ", "fb MKBZ"], node="writer", seq=6))
    self.assertEqual(victims(t, ["B"]), set())
    self.assertEqual(victims(t, ["B"], Rules(split=False)), {"proof@A"})
    self.assertEqual(victims(t), {"writer@B"})
    spec = spec_dict(t, ["A"])
    self.assertEqual(spec["boards"]["msgs#A<-writer@A"],
                     {"readers": ["proof@A", "writer@B"], "writers": ["writer@A"]})
    self.assertEqual(spec["boards"]["msgs#A<-proof@B"],
                     {"readers": ["writer@B"], "writers": ["proof@B"]})

  def test_reader_without_a_recorded_writer_uses_the_whole_board(self):
    """Text appended to a channel value in place reaches a reader without a recorded write."""
    t = trace(start("t1", "A", node="w"),
              acc("t1", "A", "msgs", "write", ["old"], node="w", seq=2),
              acc("t2", "B", "msgs", "read", ["old", "new MKAZ"], node="r", seq=3))
    self.assertEqual(victims(t), {"r@B"})
    self.assertEqual(spec_dict(t, ["A"])["boards"]["msgs#A"],
                     {"readers": ["r@B"], "writers": ["w@A"]})

  def test_state_boards_are_per_thread(self):
    """A marker in another thread's copy of a state key carries no flow, as in agents-from-scratch
    where each sender has its own thread."""
    t = trace(start("t1", "A", node="llm"),
              acc("t1", "A", "messages", "write", ["MKAZ"], node="llm", thread="tA", seq=2),
              acc("t2", "B", "messages", "read", ["MKAZ"], node="llm", thread="tB", seq=3))
    self.assertEqual(victims(t), set())
    self.assertEqual(spec_dict(t, ["A"])["boards"]["messages#A/tB"],
                     {"readers": ["llm@B"], "writers": []})
    same = trace(*(dataclasses.replace(a, thread="tA") for a in t.accesses))
    self.assertEqual(victims(same), {"llm@B"})

  def test_store_boards_are_cross_thread(self):
    value = {"r": "MKAZ"}
    t = trace(start("t1", "A", node="mem"),
              acc("t1", "A", "store:prefs", "write", value, node="mem", thread="tA", seq=2),
              acc("t2", "B", "store:prefs", "read", value, node="tri", thread="tB", seq=3))
    self.assertEqual(boards_on(findings(to_spec(t, ["A"]))["tri@B"]),
                     ["in#A", "store:prefs#A<-mem@A"])

  def test_cross_reads_see_what_markers_miss(self):
    """A's stop leaves `trials` at 3, which B's writer reads, as in kaymen99."""
    t = trace(acc("t1", "A", "trials", "write", 3, node="writer", seq=1),
              acc("t2", "A", "trials", "write", 3, node="relay", seq=2),
              acc("t3", "B", "trials", "read", 3, node="writer", seq=3),
              acc("t3", "B", "trials", "write", 4, node="writer", seq=4),
              acc("t4", "B", "trials", "read", 4, node="route", seq=5))
    t = dataclasses.replace(t, relays=frozenset({("0", "t2")}))
    self.assertEqual(cross_reads(t), {("A", "trials", "writer@B", "writer@A")})
    self.assertEqual(victims(t), set())

  def test_raw_text_counts_in_a_run_without_it(self):
    t = trace(acc("t1", "A", "email", "read", "hi MKAZ", run="a"),
              acc("t1", "A", "store:m", "write", "hi MKAZ", run="a"),
              acc("t2", "B", "store:m", "read", "hi MKAZ", run="b"),
              inputs={"a": {"email": "hi MKAZ"}, "b": {"email": "yo MKBZ"}})
    self.assertEqual(victims(t), {"n@B"})

  def test_spec_shape(self):
    t = trace(acc("t1", "A", "k", "write", "MKAZ"))
    spec = spec_dict(t, ["A"])
    self.assertEqual(spec["agents"], ["input@A", "input@B", "n@A"])
    self.assertEqual(spec["adversary"], {"controls": ["input@A"]})
    self.assertEqual(spec["boards"], {"in#A": {"readers": [], "writers": ["input@A"]},
                                      "in#B": {"readers": [], "writers": ["input@B"]}})

  def test_unknown_attacker_rejected(self):
    with self.assertRaises(ValueError):
      spec_dict(trace(), ["C"])

  def test_task_id_of(self):
    self.assertEqual(task_id_of("outer:p1|inner:t2"), "t2")
    self.assertEqual(task_id_of("a:t1"), "t1")
    self.assertIsNone(task_id_of(""))


class EventTests(unittest.TestCase):
  def events(self, result):
    return [
      ((), {"type": "task", "payload": {"id": "p", "name": "sub", "input": {"k": ""}}}),
      (("sub:p",), {"type": "task", "payload": {"id": "c", "name": "inner",
                                                "input": {"k": "MKAZ"}}}),
      (("sub:p",), {"type": "task_result", "payload": {"id": "c", "name": "inner",
                                                       "result": result}}),
      ((), {"type": "checkpoint", "payload": {}}),
    ]

  def test_dict_and_pair_results_agree(self):
    """Untracked tasks fall back to their whole input, and the subgraph task reads nothing."""
    for result in ({"k": "MKBZ", "branch:to:x": None}, [("k", "MKBZ"), ("branch:to:x", None)]):
      t = trace_from_events("0", self.events(result), [], MARKERS, principal="A")
      self.assertEqual([(a.node, a.mode, a.channel, a.value) for a in t.accesses],
                       [("sub/inner", "read", "k", "MKAZ"), ("sub/inner", "write", "k", "MKBZ")])
      self.assertEqual(t.fallbacks, {"sub/inner@A"})

  def test_tracked_reads_replace_the_input(self):
    reads = [ReadOp("c", "j", "x", seq=1), ReadOp("c", "k", "MKAZ", seq=3, route=True),
             ReadOp("zz", "k", "", seq=4)]
    events = [Stamped(i * 2, ev) for i, ev in enumerate(self.events({"k": "MKBZ"}))]
    t = trace_from_events("0", events, [], MARKERS, principal="A", reads=reads, tracked=["c"],
                          thread="t")
    self.assertEqual([(a.node, a.mode, a.channel, a.seq, a.thread) for a in t.accesses],
                     [("sub/inner", "read", "j", 1, "t"), ("sub/inner", "write", "k", 4, "t"),
                      ("sub/inner", "read", "k", 5, "t")])
    self.assertEqual((t.fallbacks, t.unattributed), (frozenset(), 1))

  def test_child_inherits_parent_principal_and_store_ops_resolve(self):
    def principal_of(node, _input):
      return "B" if node == "sub" else None
    ops = [StoreOp("c", ("ns",), "write", {"v": 1}), StoreOp(None, ("ns",), "read", None)]
    t = trace_from_events("0", self.events({}), ops, MARKERS, principal="A",
                          principal_of=principal_of)
    self.assertEqual({(a.agent, a.channel) for a in t.accesses},
                     {("sub/inner@B", "k"), ("sub/inner@B", "store:ns")})
    self.assertEqual(t.unattributed, 1)


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class MarkerLLMTests(unittest.TestCase):
  def test_copies_markers_and_follows_script(self):
    from pydantic import BaseModel

    class Router(BaseModel):
      route: Literal["ignore", "respond"]
      reasoning: str

    llm = marker_llm(MARKERS, {"Router": {"route": "ignore"}, "text": "draft {markers}!"})
    self.assertEqual(llm.invoke("from MKBZ").content, "draft MKBZ!")
    out = llm.with_structured_output(Router).invoke("from MKAZ")
    self.assertEqual((out.route, out.reasoning), ("ignore", "[fake] MKAZ"))

  def test_router_scripts(self):
    self.assertEqual(router_scripts({"R": ["x", "y"], "S": [1]}),
                     ({"R": "x", "S": 1}, {"R": "y", "S": 1}))


def owner(text):
  return next((p for p, m in MARKERS.items() if m in text), None)


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class BatchedClearTests(unittest.TestCase):
  """One run handles A's then B's email, as in kaymen99. `msgs` must be emptied between them."""

  def subject(self, clear):
    from langchain_core.messages import HumanMessage, RemoveMessage
    from langgraph.graph import END, START, StateGraph
    from langgraph.graph.message import add_messages

    class S(TypedDict):
      inbox: list[str]
      current: str
      msgs: Annotated[list, add_messages]

    def build(store, script):
      llm = marker_llm(MARKERS, script)

      def load(s):
        return {"current": s["inbox"][0], "inbox": s["inbox"][1:]}

      def write(s):
        prompt = [*s["msgs"], HumanMessage(s["current"])]
        return {"msgs": [prompt[-1], llm.invoke(prompt)]}

      def route(s):
        if not s["inbox"]:
          return END
        if clear == "routing":
          s["msgs"] = []
          return "load"
        return "reset"

      def reset(s):
        """Remove by id, since langgraph 0.2 has no `REMOVE_ALL_MESSAGES`. It still serves A."""
        if clear != "remove":
          return {"msgs": []}
        return {"msgs": [RemoveMessage(id=m.id) for m in s["msgs"]]}

      g = StateGraph(S)
      g.add_node("load", load)
      g.add_node("write", write)
      g.add_node("reset", reset)
      g.add_edge(START, "load")
      g.add_edge("load", "write")
      g.add_conditional_edges("write", route, ["load", "reset", END])
      g.add_edge("reset", "load")
      return instrument(g).compile(store=store)

    def principal_of(node, s):
      return owner(s["inbox"][0]) if node == "load" else owner(s["current"])

    inbox = [f"hi from {MARKERS['A']}", f"hello from {MARKERS['B']}"]
    run = Run({"inbox": inbox, "current": "", "msgs": []})
    return Subject(build, (run,), MARKERS, frozenset({"A"}), principal_of=principal_of)

  def test_clear_in_routing_function_leaks(self):
    t = trace_subject(self.subject("routing"))
    found = findings(to_spec(t, ["A"]))
    self.assertEqual(boards_on(found["write@B"]), ["in#A", "msgs#A/run0<-write@A"])
    self.assertEqual(t.fallbacks, frozenset())

  def test_empty_list_does_not_clear_add_messages(self):
    self.assertIn("write@B", findings(extract(self.subject("empty"))))

  def test_remove_messages_fixes_it(self):
    t = trace_subject(self.subject("remove"))
    self.assertEqual(findings(to_spec(t, ["A"])), {})
    self.assertEqual(flows(t), frozenset())
    self.assertIn("reset@A", {a.agent for a in t.accesses})


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class StoreRouterTests(unittest.TestCase):
  """One run per sender sharing a store, as in agents-from-scratch."""

  def subject(self, scripts):
    from langgraph.config import get_store
    from langgraph.graph import END, START, StateGraph
    from pydantic import BaseModel

    class Router(BaseModel):
      route: Literal["ignore", "respond"]
      reasoning: str

    class S(TypedDict, total=False):
      email: str
      route: str
      reply: str

    def build(store, script):
      llm = marker_llm(MARKERS, script)

      def triage(s):
        item = get_store().get(("prefs",), "rules")
        rules = item.value["rules"] if item else ""
        return {"route": llm.with_structured_output(Router).invoke(f"{rules}\n{s['email']}").route}

      def remember(s):
        get_store().put(("prefs",), "rules", {"rules": llm.invoke(s["email"]).content})
        return {}

      def respond(s):
        return {"reply": llm.invoke(s["email"]).content}

      g = StateGraph(S)
      g.add_node("triage", triage)
      g.add_node("remember", remember)
      g.add_node("respond", respond)
      g.add_edge(START, "triage")
      g.add_conditional_edges("triage", lambda s: "remember" if s["route"] == "ignore"
                              else "respond", ["remember", "respond"])
      g.add_edge("remember", END)
      g.add_edge("respond", END)
      return instrument(g).compile(store=store)

    runs = (Run({"email": f"spam {MARKERS['A']}"}, "A"), Run({"email": f"hi {MARKERS['B']}"}, "B"))
    return Subject(build, runs, MARKERS, frozenset({"A"}), scripts=scripts)

  def test_store_ops_carry_their_task(self):
    t = trace_subject(self.subject(({"Router": {"route": "ignore"}},)))
    store = {(a.agent, a.mode) for a in t.accesses if a.channel == "store:prefs"}
    self.assertEqual(store, {("remember@A", "write"), ("remember@B", "write"),
                             ("triage@A", "read"), ("triage@B", "read")})
    self.assertEqual(t.unattributed, 0)

  def test_only_the_ignore_branch_leaks(self):
    scripts = router_scripts({"Router": [{"route": "ignore"}, {"route": "respond"}]})
    self.assertEqual(set(findings(extract(self.subject(scripts[1:])))), set())
    found = findings(extract(self.subject(scripts)))
    self.assertEqual(boards_on(found["triage@B"]), ["in#A", "store:prefs#A<-remember@A"])

  def test_recording_store_outside_a_graph(self):
    store = recording_store()
    store.put(("x",), "k", {"v": "MKAZ"})
    self.assertEqual(store.get(("x",), "k").value, {"v": "MKAZ"})
    self.assertEqual([(o.task, o.mode) for o in store.ops], [(None, "write"), (None, "read")])


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class ReadTrackingTests(unittest.TestCase):
  """What `instrument` records on small graphs."""

  def run_graph(self, build, inp, principal="A", config=None):
    return trace_subject(Subject(build, (Run(inp, principal, config),), MARKERS,
                                 frozenset({"A"})))

  def reads(self, t):
    return {(a.agent, a.channel) for a in t.accesses if a.mode == "read"}

  def typed_graph(self, node, route=None, wrap=True):
    from langgraph.graph import END, START, StateGraph

    class S(TypedDict, total=False):
      a: str
      b: str
      c: str

    def build(store, script):
      g = StateGraph(S)
      g.add_node("n", node)
      g.add_node("m", lambda s: {})
      g.add_edge(START, "n")
      if route:
        g.add_conditional_edges("n", route, ["m"])
      else:
        g.add_edge("n", "m")
      g.add_edge("m", END)
      return (instrument(g) if wrap else g).compile(store=store)
    return build

  def test_only_accessed_keys_are_read(self):
    inp = {"a": "MKAZ", "b": "MKBZ", "c": ""}
    t = self.run_graph(self.typed_graph(lambda s: {"c": s["a"] + s.get("zz", "")}), inp)
    self.assertEqual(self.reads(t), {("n@A", "a")})
    self.assertEqual(t.fallbacks, frozenset())

  def test_uninstrumented_graph_falls_back_with_a_warning(self):
    build = self.typed_graph(lambda s: {"c": s["a"]}, wrap=False)
    with self.assertWarns(UserWarning):
      t = self.run_graph(build, {"a": "MKAZ", "b": "x", "c": ""})
    self.assertEqual(self.reads(t), {(f"{n}@A", k) for n in "nm" for k in "abc"})
    self.assertEqual(t.fallbacks, {"n@A", "m@A"})

  def test_routing_function_reads_belong_to_its_source_task(self):
    t = self.run_graph(self.typed_graph(lambda s: {"c": "x"}, route=lambda s: s["b"] and "m"),
                       {"a": "", "b": "MKAZ", "c": ""})
    route = [a for a in t.accesses if a.channel == "b"]
    write = next(a for a in t.accesses if a.channel == "c" and a.mode == "write")
    self.assertEqual([(a.agent, a.mode) for a in route], [("n@A", "read")])
    self.assertGreater(route[0].seq, write.seq)

  def test_returning_the_state_is_a_relay_not_a_read(self):
    t = self.run_graph(self.typed_graph(lambda s: s), {"a": "MKAZ", "b": "", "c": ""})
    self.assertEqual(self.reads(t), set())
    self.assertEqual({a.channel for a in t.accesses if a.agent == "n@A"}, {"a", "b", "c"})
    self.assertEqual(len(t.relays), 1)

  def test_copying_the_state_reads_every_key(self):
    t = self.run_graph(self.typed_graph(lambda s: {"c": str(len({**s}))}),
                       {"a": "MKAZ", "b": "", "c": ""})
    self.assertEqual(self.reads(t), {("n@A", k) for k in "abc"})

  def test_pydantic_state_attribute_reads(self):
    from langgraph.graph import END, START, StateGraph
    from pydantic import BaseModel

    class P(BaseModel):
      a: str = ""
      b: str = ""

    def build(store, script):
      g = StateGraph(P)
      g.add_node("n", lambda s: {"b": s.a + str(isinstance(s, P))})
      g.add_edge(START, "n")
      g.add_edge("n", END)
      return instrument(g).compile(store=store)
    t = self.run_graph(build, {"a": "MKAZ"})
    self.assertEqual(self.reads(t), {("n@A", "a")})
    self.assertIn(("n@A", "b", "MKAZTrue"),
                  {(a.agent, a.channel, a.value) for a in t.accesses if a.mode == "write"})

  def test_compiled_subgraph_node_is_instrumented(self):
    from langgraph.graph import END, START, StateGraph

    class S(TypedDict, total=False):
      a: str
      b: str

    inner = StateGraph(S)
    inner.add_node("leaf", lambda s: {"b": s["a"]})
    inner.add_edge(START, "leaf")
    inner.add_edge("leaf", END)
    sub = inner.compile()

    def build(store, script):
      g = StateGraph(S)
      g.add_node("sub", sub)
      g.add_edge(START, "sub")
      g.add_edge("sub", END)
      return instrument(g).compile(store=store)
    t = self.run_graph(build, {"a": "MKAZ", "b": ""})
    self.assertEqual(self.reads(t), {("sub/leaf@A", "a")})
    self.assertEqual(t.fallbacks, frozenset())

  def test_threads_name_state_boards(self):
    from langgraph.checkpoint.memory import InMemorySaver
    from langgraph.graph import END, START, StateGraph

    class S(TypedDict, total=False):
      email: str
      notes: str

    def build(store, script):
      g = StateGraph(S)
      g.add_node("note", lambda s: {"notes": f"{s.get('notes', '')} {s['email']}!"})
      g.add_node("read", lambda s: {"email": s["notes"]})
      g.add_edge(START, "note")
      g.add_edge("note", "read")
      g.add_edge("read", END)
      return instrument(g).compile(store=store, checkpointer=InMemorySaver())
    runs = tuple(Run({"email": f"hi {MARKERS[p]}"}, p, {"configurable": {"thread_id": f"t{p}"}})
                 for p in "AB")
    t = trace_subject(Subject(build, runs, MARKERS, frozenset({"A"})))
    boards = spec_dict(t, ["A"])["boards"]
    self.assertIn("notes#A/tA<-note@A", boards)
    self.assertEqual(findings(to_spec(t, ["A"])), {})


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class ResumeTests(unittest.TestCase):
  def test_resume_after_interrupt_is_traced(self):
    from langgraph.checkpoint.memory import InMemorySaver
    from langgraph.graph import END, START, StateGraph
    from langgraph.types import interrupt

    class S(TypedDict, total=False):
      email: str
      answer: str

    def build(store, script):
      g = StateGraph(S)
      g.add_node("ask", lambda s: {"answer": interrupt(s["email"])})
      g.add_node("after", lambda s: {"email": s["answer"]})
      g.add_edge(START, "ask")
      g.add_edge("ask", "after")
      g.add_edge("after", END)
      return instrument(g).compile(store=store, checkpointer=InMemorySaver())

    run = Run({"email": "MKAZ"}, "A", {"configurable": {"thread_id": "t"}}, ("ok MKAZ",))
    t = trace_subject(Subject(build, (run,), MARKERS, frozenset({"A"})))
    self.assertIn(("after@A", "answer", "ok MKAZ"),
                  {(a.agent, a.channel, a.value) for a in t.accesses if a.mode == "read"})


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class InPlaceMutationTests(unittest.TestCase):
  """A routing function pops the inbox in place, as kaymen99's `must_rewrite` does."""

  def test_task_input_is_recorded_as_it_was(self):
    from langgraph.graph import END, START, StateGraph

    class S(TypedDict):
      inbox: list[str]

    def route(s):
      s["inbox"].pop()
      return "pick" if s["inbox"] else END

    def build(store, script):
      g = StateGraph(S)
      g.add_node("pick", lambda s: {})
      g.add_edge(START, "pick")
      g.add_conditional_edges("pick", route, ["pick", END])
      return instrument(g).compile(store=store)

    run = Run({"inbox": ["hi MKBZ", "hi MKAZ"]})
    subject = Subject(build, (run,), MARKERS, frozenset({"A"}),
                      principal_of=lambda node, s: owner(s["inbox"][-1]) if s["inbox"] else None)
    reads = [a.agent for a in trace_subject(subject).accesses if a.mode == "read"]
    self.assertEqual(list(dict.fromkeys(reads)), ["pick@A", "pick@B"])


def resource_trace(mark, run_input, principal=None):
  """The resource log since `mark` as a trace with no LangGraph events."""
  ops, tasks, calls = RESOURCES.since(mark)
  return trace_from_events("0", [], ops, MARKERS, run_input, principal, external=tasks,
                           calls=calls)


class ResourceTests(unittest.TestCase):
  """Recorders for state kept outside LangGraph. None of them needs LangGraph."""

  def setUp(self):
    self.root = tempfile.mkdtemp()
    self.mark = RESOURCES.mark()

  def path(self, *parts):
    return os.path.join(self.root, *parts)

  def save_atomically(self, name, data):
    """Write through a temporary file and rename it, as DeerFlow's `FileMemoryStorage` does."""
    tmp = self.path(name + ".tmp")
    with open(tmp, "w") as f:
      json.dump(data, f)
    os.replace(tmp, self.path(name))

  def test_file_written_by_one_principal_reaches_another(self):
    with FileRecorder(self.root):
      with acting("updater", principal="A"):
        self.save_atomically("memory.json", {"facts": ["A said MKAZ"]})
      with acting("prompt", principal="B"):
        with open(self.path("memory.json")) as f:
          f.read()
    t = resource_trace(self.mark, {})
    self.assertEqual([(a.agent, a.channel, a.mode) for a in t.accesses
                      if a.channel == "file:memory.json"],
                     [("updater@A", "file:memory.json", "write"),
                      ("prompt@B", "file:memory.json", "read")])
    self.assertEqual(t.accesses[-1].value, {"facts": ["A said MKAZ"]})
    t = dataclasses.replace(t, accesses=(acc("t0", "A", "msg", "read", "MKAZ", node="updater"),
                                         *t.accesses), inputs={"0": {"msg": "MKAZ"}})
    path = findings(to_spec(t, ["A"]))["prompt@B"]
    self.assertEqual(boards_on(path)[-1], "file:memory.json#A<-updater@A")

  def test_files_outside_the_root_and_directories_are_ignored(self):
    outside = tempfile.mkdtemp()
    os.mkdir(self.path("sub"))
    with FileRecorder(self.root):
      with acting("w", principal="A"):
        with open(os.path.join(outside, "x.txt"), "w") as f:
          f.write("MKAZ")
        with open(self.path("sub", "y.txt"), "w") as f:
          f.write("MKAZ")
    self.assertEqual([op.where for op in RESOURCES.since(self.mark)[0]], ["file:sub/y.txt"])

  def test_pending_write_lands_at_the_next_open(self):
    with FileRecorder(self.root):
      with acting("w", principal="A"):
        with open(self.path("log.txt"), "w") as f:
          f.write("first MKAZ")
      with acting("r", principal="B"):
        with open(self.path("log.txt")) as f:
          f.read()
      with acting("w2", principal="B"):
        with open(self.path("log.txt"), "a") as f:
          f.write(" then MKBZ")
    ops = [(op.mode, op.value) for op in RESOURCES.since(self.mark)[0]]
    self.assertEqual(ops, [("write", "first MKAZ"), ("read", "first MKAZ"),
                           ("write", "first MKAZ then MKBZ")])

  def test_context_variables_do_not_cross_a_thread_and_a_handoff_does(self):
    handoff, seen = Handoff("queue:q"), {}
    def consume():
      seen["bare"] = current_task()
      with handoff.receive("k", "consumer", ["MKAZ"]):
        emit("store:out", "write", "MKAZ")
    with acting("producer", principal="A"):
      handoff.send("k", ["MKAZ"])
      worker = threading.Thread(target=consume)
      worker.start()
      worker.join()
    self.assertIsNone(seen["bare"])
    t = resource_trace(self.mark, {})
    self.assertEqual([(a.agent, a.channel, a.mode) for a in t.accesses],
                     [("producer@A", "queue:q", "write"), ("consumer@A", "queue:q", "read"),
                      ("consumer@A", "store:out", "write")])

  def test_acting_follows_asyncio_to_thread(self):
    async def body():
      with acting("job", principal="B"):
        await asyncio.to_thread(emit, "store:x", "write", "v")
    asyncio.run(body())
    t = resource_trace(self.mark, {})
    self.assertEqual([a.agent for a in t.accesses], ["job@B"])

  def test_external_task_inherits_its_parent_or_the_run_and_an_unknown_parent_is_lost(self):
    ext = [ExternalTask("p", "parent", None, None, 1), ExternalTask("c", "child", None, "p", 2),
           ExternalTask("o", "orphan", None, "gone", 3)]
    ops = [StoreOp(t, (), "write", "v", 4 + i, "store:x") for i, t in enumerate("pco")]
    t = trace_from_events("0", [], ops, MARKERS, principal="B", external=ext)
    self.assertEqual([a.agent for a in t.accesses], ["parent@B", "child@B"])
    self.assertEqual(t.unattributed, 2)

  def test_built_value_is_read_by_the_llm_call_that_contains_it(self):
    prompt = "You are helpful.\n<memory>\n- A said MKAZ\n</memory>"
    ops = [StoreOp("f", (), "write", prompt, 2, "built:agent")]
    calls = [LLMCall("m", [{"role": "system", "content": prompt + " today"}], 3),
             LLMCall("other", ["no memory here"], 4)]
    ext = [ExternalTask("f", "factory", "B", None, 1), ExternalTask("m", "model", "B", None, 1),
           ExternalTask("other", "title", "B", None, 1)]
    t = trace_from_events("0", [], ops, MARKERS, external=ext, calls=calls)
    self.assertEqual([(a.agent, a.mode) for a in t.accesses],
                     [("factory@B", "write"), ("model@B", "read")])

  def test_a_cache_above_the_file_hides_the_read_and_the_markers_show_it(self):
    """A store with an in-process cache, as DeerFlow's `FileMemoryStorage` has. The file seam
    misses the cached load, and `unexplained` reports the flow it left without a path. Wrapping
    the store's own `load` with `recorded` sees it."""
    root = self.root

    class CachingStore:
      cache = None

      def load(self):
        if self.cache is None:
          with open(os.path.join(root, "m.json")) as f:
            self.cache = json.load(f)
        return self.cache

      def save(self, data):
        with open(os.path.join(root, "m.json"), "w") as f:
          json.dump(data, f)
        self.cache = data

    def run(store):
      mark = RESOURCES.mark()
      with FileRecorder(root):
        with acting("updater", principal="A"):
          store.save({"fact": "A wrote MKAZ"})
        with acting("agent", principal="B"):
          emit("store:out", "write", store.load()["fact"])
        with acting("reader", principal="B"):
          emit("store:out", "read", "A wrote MKAZ")
      t = resource_trace(mark, {})
      return dataclasses.replace(
        t, accesses=(acc("t0", "A", "msg", "read", "MKAZ", node="updater"), *t.accesses),
        inputs={"0": {"msg": "MKAZ"}})

    files_only = run(CachingStore())
    self.assertEqual(unexplained(files_only, ["A"]), {("A", "store:out", "reader@B")})
    self.assertEqual(victims(files_only), set())

    class Recorded(CachingStore):
      load = recorded(CachingStore.load, "read", lambda *a: "ext:store")
      save = recorded(CachingStore.save, "write", lambda *a: "ext:store")

    both = run(Recorded())
    self.assertEqual(unexplained(both, ["A"]), frozenset())
    self.assertEqual(victims(both), {"agent@B", "reader@B"})
    self.assertIn(("A", "ext:store", "agent@B"), shared_reads(both))


if __name__ == "__main__":
  unittest.main()
