"""The ordered analysis input from `lgtrace.ordered_dict`, the analysis in `ordered.py` and its
Lean export `lean_export.to_lean_ordered`."""

import importlib.util
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import TypedDict

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import irspec  # noqa: E402
import lean_export  # noqa: E402
import ordered  # noqa: E402
from lgtrace import (  # noqa: E402
  Access, Graph, Run, Subject, Trace, findings, instrument, marker_llm, node_facts,
  ordered_dict, pass_through_keys, to_spec, trace_subject)

HAS_LANGGRAPH = importlib.util.find_spec("langgraph") is not None
MARKERS = {"A": "MKAZ", "B": "MKBZ"}
IR_DIR = Path(__file__).resolve().parents[2] / "proofs"


def acc(task, principal, channel, mode, value, node, seq, run="0.0", thread="t"):
  return Access(run, task, node, principal, channel, mode, value, thread, seq)


def aix_trace(passes=True, step_of_exec=3):
  """Aix-DB's shape. `parse` (code) puts the run's own rows in `meta` and the shared `db`, `gen`
  (LLM) reads `meta`, `exec` (code) reads the attacker B's rows from `db` into `result` and
  writes `meta` back unchanged. `gen@A` reads `meta` through the whole board, since no recorded
  write holds its string, so `Reach` links it to `exec@A`."""
  def run(p, r, base):
    t = lambda n: f"{n}{p}"  # noqa: E731
    return [
      acc(t("parse"), p, "q", "read", f"q {MARKERS[p]}", "parse", base + 1, r, f"chat{p}"),
      acc(t("parse"), p, "db:rows", "write", f"row {MARKERS[p]}", "parse", base + 2, r),
      acc(t("parse"), p, "meta", "write", "m", "parse", base + 3, r, f"chat{p}"),
      acc(t("gen"), p, "meta", "read", f"meta {MARKERS[p]}", "gen", base + 4, r, f"chat{p}"),
      acc(t("gen"), p, "sql", "write", "select", "gen", base + 5, r, f"chat{p}"),
      acc(t("exec"), p, "sql", "read", "select", "exec", base + 6, r, f"chat{p}"),
      acc(t("exec"), p, "db:rows", "read", f"row {MARKERS['B']}", "exec", base + 7, r),
      acc(t("exec"), p, "result", "write", f"res {MARKERS['B']}", "exec", base + 8, r,
          f"chat{p}"),
      acc(t("exec"), p, "meta", "write", f"meta {MARKERS[p]}", "exec", base + 9, r, f"chat{p}"),
      acc(t("sum"), p, "result", "read", f"res {MARKERS['B']}", "sum", base + 10, r, f"chat{p}"),
    ]
  accesses = run("B", "0.0", 0) + run("A", "0.1", 100)
  tasks = {(a.run, a.task) for a in accesses}
  steps = {}
  for a in accesses:
    steps[(a.run, a.task)] = {"parse": 1, "gen": 2, "exec": step_of_exec, "sum": 4}[a.node]
  spans = {}
  for a in accesses:
    lo, hi = spans.get((a.run, a.task), (a.seq, a.seq))
    spans[(a.run, a.task)] = (min(lo, a.seq), max(hi, a.seq))
  return Trace(
    MARKERS, {"0.0": {"q": f"q {MARKERS['B']}"}, "0.1": {"q": f"q {MARKERS['A']}"}},
    tuple(accesses), tracked=frozenset(tasks),
    llm_tasks=frozenset((a.run, a.task, a.node) for a in accesses if a.node in ("gen", "sum")),
    passes=frozenset((a.run, a.task, "meta") for a in accesses
                     if passes and a.node == "exec" and a.channel == "meta"),
    graphs=(Graph(frozenset({"parse", "gen", "exec", "sum"}),
                  {k: "LastValue" for k in ("q", "meta", "sql", "result")}),),
    steps=steps, spans=spans)


class NodeFactsTests(unittest.TestCase):

  def test_kinds_passes_and_kills(self):
    f = node_facts(aix_trace())
    self.assertEqual({n: x.kind for n, x in f.items()},
                     {"parse": "code", "gen": "llm", "exec": "code", "sum": "llm"})
    self.assertEqual(f["exec"].passes, {"meta"})
    self.assertEqual(f["exec"].kills, {"result"})
    self.assertEqual(f["parse"].kills, {"meta"})
    self.assertEqual(f["gen"].kills, frozenset())

  def test_untracked_task_makes_its_node_opaque(self):
    t = aix_trace()
    t = Trace(t.markers, t.inputs, t.accesses, tracked=t.tracked - {("0.1", "execA")},
              llm_tasks=t.llm_tasks, passes=t.passes, graphs=t.graphs, steps=t.steps,
              spans=t.spans)
    self.assertEqual(node_facts(t)["exec"].kind, "opaque")

  def test_a_reducer_channel_is_never_killed(self):
    t = aix_trace()
    graphs = (Graph(t.graphs[0].nodes, {**t.graphs[0].channels,
                                        "result": "BinaryOperatorAggregate"}),)
    t = Trace(t.markers, t.inputs, t.accesses, tracked=t.tracked, llm_tasks=t.llm_tasks,
              passes=t.passes, graphs=graphs, steps=t.steps, spans=t.spans)
    self.assertEqual(node_facts(t)["exec"].kills, frozenset())

  def test_a_key_another_graph_declares_is_never_killed(self):
    t = aix_trace()
    graphs = (*t.graphs, Graph(frozenset({"other"}), {"result": "LastValue"}))
    t = Trace(t.markers, t.inputs, t.accesses, tracked=t.tracked, llm_tasks=t.llm_tasks,
              passes=t.passes, graphs=graphs, steps=t.steps, spans=t.spans)
    self.assertEqual(node_facts(t)["exec"].kills, frozenset())

  def test_a_key_written_only_sometimes_is_never_killed(self):
    t = aix_trace()
    kept = tuple(a for a in t.accesses
                 if not (a.task == "execA" and a.channel == "result"))
    t = Trace(t.markers, t.inputs, kept, tracked=t.tracked, llm_tasks=t.llm_tasks,
              passes=t.passes, graphs=t.graphs, steps=t.steps, spans=t.spans)
    self.assertEqual(node_facts(t)["exec"].kills, frozenset())


class AixShapeTests(unittest.TestCase):
  """The false positive of Aix-DB, on a hand-made trace."""

  def report(self, trace):
    return ordered.report(ordered_dict(trace, ["B"]))

  def test_reach_reports_the_generator(self):
    self.assertEqual(findings(to_spec(aix_trace(), ["B"])).keys(),
                     {"exec@A", "gen@A", "sum@A"})

  def test_summary_drops_the_generator_and_keeps_the_leak(self):
    r = self.report(aix_trace())
    self.assertEqual(r["every"], ["exec@A", "sum@A"])
    self.assertEqual(r["summary"], ["exec@A", "sum@A"])
    self.assertEqual(r["dropped"]["every"], ["gen@A"])
    self.assertEqual(r["missed"], {"order": [], "summary": [], "every": []})

  def test_order_alone_drops_it_only_on_the_traced_order(self):
    r = self.report(aix_trace(passes=False))
    self.assertEqual(r["order"], ["exec@A", "sum@A"])
    self.assertEqual(r["every"], ["exec@A", "gen@A", "sum@A"])

  def test_a_generator_after_the_executor_is_reached(self):
    r = self.report(aix_trace(passes=False, step_of_exec=1))
    self.assertIn("gen@A", r["order"])

  def test_pass_through_output_depends_on_the_key_it_copies(self):
    d = ordered_dict(aix_trace(), ["B"])
    self.assertEqual(d["summaries"]["exec@A"]["dep"], {"meta#A/chatA": []})
    self.assertEqual(d["summaries"]["gen@A"], {"kind": "llm", "dep": {}, "passes": [],
                                                "kills": []})


class ScheduleTests(unittest.TestCase):

  def test_supersteps_order_turns_despite_late_events(self):
    t = aix_trace()
    late = tuple(Access(a.run, a.task, a.node, a.principal, a.channel, a.mode, a.value,
                        a.thread, a.seq + (1000 if a.mode == "write" else 0))
                 for a in t.accesses)
    spans = {k: (lo, lo) for k, (lo, _) in t.spans.items()}
    t = Trace(t.markers, t.inputs, late, tracked=t.tracked, llm_tasks=t.llm_tasks,
              passes=t.passes, graphs=t.graphs, steps=t.steps, spans=spans)
    turns = ordered_dict(t, ["B"])["schedules"][0]["turns"]
    self.assertEqual([x["agent"] for x in turns],
                     [f"{n}@{p}" for p in "BA" for n in ("parse", "gen", "exec", "sum")])
    self.assertEqual(len({x["cluster"] for x in turns}), 8)

  def test_a_shared_superstep_is_one_cluster_without_kills(self):
    turns = ordered_dict(aix_trace(step_of_exec=2), ["B"])["schedules"][0]["turns"]
    together = [x for x in turns if x["agent"] in ("gen@A", "exec@A")]
    self.assertEqual(len({x["cluster"] for x in together}), 1)
    self.assertEqual([x["kills"] for x in together], [[], []])
    alone = next(x for x in turns if x["agent"] == "parse@B")
    self.assertEqual(alone["kills"], ["meta#B/chatB"])

  def test_an_external_task_overlapping_a_node_joins_its_cluster(self):
    t = aix_trace()
    ext = acc("ext", "A", "db:rows", "read", "x", "updater", 103, "0.1")
    spans = {**t.spans, ("0.1", "ext"): (103, 150)}
    t = Trace(t.markers, t.inputs, (*t.accesses, ext), tracked=t.tracked,
              llm_tasks=t.llm_tasks, passes=t.passes, graphs=t.graphs, steps=t.steps,
              spans=spans)
    turns = ordered_dict(t, ["B"])["schedules"][0]["turns"]
    cluster = next(x["cluster"] for x in turns if x["agent"] == "updater@A")
    self.assertEqual({x["agent"] for x in turns if x["cluster"] == cluster},
                     {"parse@A", "gen@A", "exec@A", "sum@A", "updater@A"})


def tiny(boards, controls=("input@B",), dep=None, schedule=(), flows=()):
  """An `ordered_dict`-shaped input from boards {name: (readers, writers)}."""
  agents = sorted({a for r, w in boards.values() for a in (*r, *w)} | set(controls))
  spec = {"agents": agents, "owner": {}, "sees": "none", "echo_sees": "none",
          "boards": {b: {"readers": sorted(r), "writers": sorted(w)}
                     for b, (r, w) in boards.items()},
          "adversary": {"controls": list(controls)}}
  summaries = {a: {"kind": "code", "dep": (dep or {}).get(a, {})} for a in agents}
  turns = [{"agent": a, "cluster": i, "kills": list(k)} for i, (a, k) in enumerate(schedule)]
  return {"spec": spec, "summaries": summaries, "schedules": [{"script": "0", "turns": turns}],
          "flows": [list(f) for f in flows]}


class AnalysisTests(unittest.TestCase):

  def test_closure_without_summaries_is_reach(self):
    names = ["x@A", "y@A", "z@A", "w@B"]
    for seed in range(40):
      combos = list(itertools.product(range(4), repeat=2))
      picked = [combos[(seed * 7 + i * 5) % len(combos)] for i in range(seed % 6 + 1)]
      boards = {f"b{i}": ({names[r]}, {names[w]}) for i, (r, w) in enumerate(picked)}
      boards["in#B"] = ({names[seed % 4]}, {"input@B"})
      d = tiny(boards)
      spec = irspec.from_dict(d["spec"])
      self.assertEqual(ordered.closure(d, summaries=False).agents, irspec.reach(spec), boards)

  def test_a_kill_between_writer_and_reader_cuts_the_flow(self):
    boards = {"in#B": ({"w@B"}, {"input@B"}), "d": ({"r@A"}, {"w@B", "reset@A"})}
    sched = [("w@B", ()), ("reset@A", ("d",)), ("r@A", ())]
    w = ordered.traced(tiny(boards, schedule=sched))[0]
    self.assertNotIn("r@A", w.taint.agents)
    late = [("w@B", ()), ("r@A", ()), ("reset@A", ("d",))]
    self.assertIn("r@A", ordered.traced(tiny(boards, schedule=late))[0].taint.agents)
    self.assertIn("r@A", ordered.closure(tiny(boards, schedule=sched)).agents)

  def test_a_cluster_runs_to_its_fixpoint(self):
    boards = {"in#B": ({"u@B"}, {"input@B"}), "p": ({"v@A"}, {"u@B"}),
              "q": ({"u@B"}, {"v@A"}), "r": ({"s@A"}, {"v@A"})}
    d = tiny(boards, schedule=[("v@A", ()), ("u@B", ()), ("s@A", ())])
    for t in d["schedules"][0]["turns"][:2]:
      t["cluster"] = 0
    w = ordered.traced(d)[0]
    self.assertIn("s@A", w.taint.agents)
    self.assertEqual([t.agent for t in w.turns][1:], ["v@A", "u@B", "v@A", "u@B", "s@A"])

  def test_a_wrong_summary_is_caught_by_the_concrete_flows(self):
    boards = {"in#B": ({"x@B"}, {"input@B"}), "m": ({"y@A"}, {"x@B"})}
    d = tiny(boards, dep={"x@B": {"m": []}}, schedule=[("x@B", ()), ("y@A", ())],
             flows=[("B", "m", "y@A", "0")])
    self.assertEqual(ordered.report(d)["missed"]["every"], [["B", "m", "y@A", "0"]])

  def test_rejects_variables(self):
    d = tiny({"in#B": ({"x@A"}, {"input@B"})})
    d["spec"]["owner"] = {"v": "x@A"}
    with self.assertRaises(ValueError):
      ordered.model(d)


class PassThroughTests(unittest.TestCase):

  def test_identity_and_no_change_make_a_pass_through(self):
    meta, rows = {"t": [1]}, [1]
    given = {"meta": meta, "rows": rows, "s": "x"}
    copies = {k: json.loads(json.dumps(v)) for k, v in given.items()}
    self.assertEqual(pass_through_keys({"meta": meta, "rows": [1], "s": "x"}, None, given,
                                       copies), ["meta", "s"])

  def test_a_value_changed_in_place_is_not_one(self):
    meta = {"t": [1]}
    given, copies = {"meta": meta}, {"meta": {"t": [1]}}
    meta["t"].append(2)
    self.assertEqual(pass_through_keys({"meta": meta}, None, given, copies), [])

  def test_an_uncopied_value_is_not_one(self):
    from lgtrace import _UNCOPIED
    meta = object()
    self.assertEqual(pass_through_keys({"m": meta}, None, {"m": meta}, {"m": _UNCOPIED}), [])

  def test_a_command_update_counts(self):
    meta = {"t": 1}

    class Command:
      update = {"meta": meta}
    self.assertEqual(pass_through_keys(Command(), None, {"meta": meta}, {"meta": {"t": 1}}),
                     ["meta"])


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class GraphTests(unittest.TestCase):
  """Aix-DB's nodes on a real graph. Each node changes the state in place and returns it."""

  def subject(self):
    from langgraph.graph import END, START, StateGraph

    class S(TypedDict, total=False):
      q: str
      meta: str
      result: str

    shared: dict[str, str] = {}

    def build(store, script):
      llm = marker_llm(MARKERS, script)

      def parse(s):
        s["meta"] = "table of " + s["q"]
        return s

      def gen(s):
        llm.invoke(s["meta"])
        return s

      def run_sql(s):
        s["result"] = shared.get("B", "")
        return s

      def keep(s):
        shared.setdefault("B", s["q"])
        return {}

      g = StateGraph(S)
      for name, fn in (("parse", parse), ("gen", gen), ("run_sql", run_sql), ("keep", keep)):
        g.add_node(name, fn)
      g.add_edge(START, "parse")
      g.add_edge("parse", "gen")
      g.add_edge("gen", "run_sql")
      g.add_edge("run_sql", "keep")
      g.add_edge("keep", END)
      return instrument(g).compile(store=store)

    runs = tuple(Run({"q": f"rows {MARKERS[p]}"}, p, {"configurable": {"thread_id": p}})
                 for p in "BA")
    return Subject(build, runs, MARKERS, frozenset({"B"}))

  def test_relayed_unchanged_keys_are_pass_throughs(self):
    t = trace_subject(self.subject())
    passed = {(t2, k) for _, t2, k in t.passes}
    kinds = {k: v for g in t.graphs for k, v in g.channels.items()}
    self.assertEqual(kinds["meta"], "LastValue")
    nodes = {a.task: a.node for a in t.accesses}
    self.assertEqual({k for t2, k in passed if nodes.get(t2) == "run_sql"}, {"q", "meta"})
    self.assertEqual({k for t2, k in passed if nodes.get(t2) == "parse"}, {"q"})
    self.assertEqual({n for _, _, n in t.llm_tasks}, {"gen"})
    self.assertEqual(len({s for s in t.steps.values()}), 4)

  def test_ordered_dict_orders_the_nodes(self):
    d = ordered_dict(trace_subject(self.subject()), ["B"])
    turns = d["schedules"][0]["turns"]
    self.assertEqual([x["agent"] for x in turns],
                     [f"{n}@{p}" for p in "BA" for n in ("parse", "gen", "run_sql", "keep")])
    self.assertEqual(d["summaries"]["run_sql@A"]["kind"], "code")
    self.assertEqual(ordered.report(d)["missed"]["every"], [])


@unittest.skipUnless(shutil.which("lake") and (IR_DIR / ".lake" / "build" / "lib" / "lean" / "Ir"
                                              / "OrderedClosed.olean").exists(),
                     "lake or the built Ir.OrderedClosed missing")
class LeanExportTests(unittest.TestCase):

  def test_the_aix_shape_checks_in_lean(self):
    text = lean_export.to_lean_ordered(ordered_dict(aix_trace(), ["B"]), "Test.AixShape")
    self.assertIn("theorem every_schedule", text)
    with tempfile.TemporaryDirectory() as tmp:
      path = Path(tmp) / "AixShape.lean"
      path.write_text(text)
      proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=IR_DIR,
                            capture_output=True, text=True, timeout=600)
    self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
    self.assertEqual(proc.stdout, "")


if __name__ == "__main__":
  unittest.main()
