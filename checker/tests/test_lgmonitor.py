import asyncio
import importlib.util
import os
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path
from typing import TypedDict

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lgmonitor import (  # noqa: E402
  Isolation, Monitor, MonitoredFiles, MonitoredHandoff, MonitorViolation, SpecPolicy, blank,
  board_channel, guarded, monitor_graph, monitored_store)

HAS_LANGGRAPH = importlib.util.find_spec("langgraph") is not None
CH = "ext:memory"


class Storage:
  """A toy app storage with one shared slot per name, like pre-fix deer-flow's memory file."""

  def __init__(self) -> None:
    self.data: dict[str, dict] = {}

  def load(self, name: str = "m") -> dict:
    return self.data.get(name, {"facts": []})

  def save(self, value: dict, name: str = "m") -> bool:
    self.data[name] = value
    return True


def wired(mode="block", policy=None):
  mon = Monitor(policy or Isolation(), mode)
  st = Storage()
  st.load = guarded(Storage.load.__get__(st), mon, "read", lambda *a, **k: CH,  # type: ignore
                    key=lambda *a, **k: "m", mask=lambda v: {"facts": []})
  save = lambda value, name="m": Storage.save(st, value, name)  # noqa: E731
  st.save = guarded(save, mon, "write",  # type: ignore
                    lambda *a, **k: CH, key=lambda *a, **k: "m",
                    value=lambda a, k, r: a[0])
  return mon, st


def as_(mon, principal, node, fn, *args):
  with mon.serving(principal), mon.acting(node):
    return fn(*args)


class PolicyTest(unittest.TestCase):
  def test_isolation(self):
    pol = Isolation(shared=("file:skills/*",))
    self.assertTrue(pol.may_read("w@A", "r@A", CH))
    self.assertFalse(pol.may_read("w@A", "r@B", CH))
    self.assertTrue(pol.may_read("w@A", "r@B", "file:skills/x.md"))
    self.assertTrue(Isolation(public=frozenset({"SYS"})).may_read("w@SYS", "r@B", CH))

  def test_board_channel(self):
    self.assertEqual(board_channel("ext:memory#A<-memory_updater@A"), "ext:memory")
    self.assertEqual(board_channel("messages#A/thread-A0<-model@A"), "messages")
    self.assertEqual(board_channel("file:a/b.md#B"), "file:a/b.md")

  SPEC = {"agents": ["u@A", "u@B", "r@A", "r@B", "input@A"],
          "boards": {"ext:memory#A<-u@A": {"readers": ["r@A"], "writers": ["u@A"]},
                     "ext:memory#A<-u@A2": {"readers": ["r@B"], "writers": ["u@A"]},
                     "in#A": {"readers": ["r@A"], "writers": ["input@A"]}},
          "owner": {}, "sees": "none", "echo_sees": "none", "adversary": {"controls": []}}

  def test_spec_principal(self):
    pol = SpecPolicy.from_spec(self.SPEC)
    self.assertTrue(pol.may_read("u@A", "r@B", CH))  # the spec's cross-principal edge
    self.assertFalse(pol.may_read("u@B", "r@A", CH))
    self.assertTrue(pol.may_read("x@B", "y@B", "anything"))  # own flows

  def test_spec_agent(self):
    pol = SpecPolicy.from_spec(self.SPEC, level="agent")
    self.assertTrue(pol.may_read("u@A", "r@A", CH))
    self.assertFalse(pol.may_read("x@A", "r@A", CH))
    self.assertTrue(pol.may_read("input@A", "r@A", "messages"))
    self.assertTrue(pol.may_write("u@A", CH))
    self.assertFalse(pol.may_write("r@A", CH))


class StorageTest(unittest.TestCase):
  def test_block_masks_then_substitutes_own_value(self):
    mon, st = wired()
    as_(mon, "A", "upd", st.save, {"facts": ["alice"]})
    self.assertEqual(as_(mon, "B", "lead", st.load), {"facts": []})
    as_(mon, "B", "upd", st.save, {"facts": ["bob"]})
    self.assertEqual(as_(mon, "A", "lead", st.load), {"facts": ["alice"]})
    self.assertEqual(as_(mon, "B", "lead", st.load), {"facts": ["bob"]})
    self.assertEqual([(v.agent, v.writers, v.action) for v in mon.violations],
                     [("lead@B", ("upd@A",), "masked"), ("lead@A", ("upd@B",), "substituted")])

  def test_substitute_is_a_copy(self):
    mon, st = wired()
    as_(mon, "A", "upd", st.save, {"facts": ["alice"]})
    as_(mon, "B", "upd", st.save, {"facts": ["bob"]})
    got = as_(mon, "A", "lead", st.load)
    got["facts"].append("mutated")
    self.assertEqual(as_(mon, "A", "lead", st.load), {"facts": ["alice"]})

  def test_latest_visible_writer_by_stamp(self):
    """Two writers the reader may read, the newer wins, whatever their names."""
    mon, st = wired()
    as_(mon, "A", "zeta", st.save, {"facts": ["old"]})
    as_(mon, "A", "alpha", st.save, {"facts": ["new"]})
    as_(mon, "B", "upd", st.save, {"facts": ["bob"]})
    self.assertEqual(as_(mon, "A", "lead", st.load), {"facts": ["new"]})

  def test_flag_and_raise(self):
    mon, st = wired("flag")
    as_(mon, "A", "upd", st.save, {"facts": ["alice"]})
    self.assertEqual(as_(mon, "B", "lead", st.load), {"facts": ["alice"]})
    self.assertEqual(mon.violations[0].action, "flagged")
    mon, st = wired("raise")
    as_(mon, "A", "upd", st.save, {"facts": ["alice"]})
    with self.assertRaises(MonitorViolation):
      as_(mon, "B", "lead", st.load)

  def test_unattributed_reader_reported_not_guessed(self):
    mon, st = wired()
    as_(mon, "A", "upd", st.save, {"facts": ["alice"]})
    self.assertEqual(st.load(), {"facts": ["alice"]})
    self.assertEqual([(u.event, u.detail) for u in mon.unseen], [("read", "no principal")])
    self.assertEqual(mon.violations, [])
    mon.fail_closed = True
    self.assertEqual(st.load(), {"facts": []})

  def test_unattributed_writer(self):
    mon, st = wired()
    st.save({"facts": ["who"]})
    self.assertEqual(as_(mon, "B", "lead", st.load), {"facts": ["who"]})
    self.assertIn(("write", "no principal"), [(u.event, u.detail) for u in mon.unseen])
    self.assertIn("value has an unattributed writer", [u.detail for u in mon.unseen])

  def test_spec_write_skipped(self):
    pol = SpecPolicy.from_spec(PolicyTest.SPEC, level="agent")
    mon, st = wired(policy=pol)
    self.assertFalse(as_(mon, "A", "r", st.save, {"facts": ["x"]}))
    self.assertEqual(st.data, {})
    self.assertEqual(mon.violations[0].action, "skipped")

  def test_blank(self):
    self.assertEqual([blank(x) for x in ("s", 3, 2.5, [1], {"a": 1}, True, object())][:6],
                     ["", 0, 0.0, [], {}, False])
    self.assertIsNone(blank(object()))


class HandoffTest(unittest.TestCase):
  def test_timer_keeps_principal(self):
    mon, st = wired()
    hand = MonitoredHandoff("queue:memory", monitor=mon)
    seen: list = []
    done = threading.Event()

    def updater(convo):
      with hand.receive_value("t1", "updater", convo) as got:
        seen.append((mon.agent(), got))
        st.save({"facts": [got]})
      done.set()

    with mon.serving("A"), mon.acting("after_agent"):
      hand.send("t1", "hello")
      threading.Timer(0.01, updater, args=("hello",)).start()
    done.wait(5)
    self.assertEqual(seen, [("updater@A", "hello")])
    self.assertEqual(mon.label(CH, "m"), frozenset({"updater@A"}))
    self.assertEqual(as_(mon, "B", "lead", st.load), {"facts": []})

  def test_unknown_sender_reported(self):
    mon = Monitor(Isolation())
    hand = MonitoredHandoff("queue:memory", monitor=mon)
    with hand.receive_value("nobody", "updater", "x") as got:
      self.assertEqual(got, "x")
      self.assertIsNone(mon.agent())
    self.assertEqual(mon.unseen[0].event, "receive")


class FilesTest(unittest.TestCase):
  def setUp(self):
    self.root = Path(tempfile.mkdtemp())
    self.mon = Monitor(Isolation())

  def under(self, principal, fn, mon=None):
    mon = mon or self.mon
    with MonitoredFiles(self.root, mon), mon.serving(principal), mon.acting("tools"):
      return fn()

  def test_read_blocked_as_absent(self):
    note = self.root / "ws" / "notes.md"
    self.under("A", lambda: (note.parent.mkdir(), note.write_text("alice")))
    with self.assertRaises(FileNotFoundError):
      self.under("B", note.read_text)
    self.assertEqual(self.under("A", note.read_text), "alice")
    self.assertEqual(self.mon.violations[0].channel, "file:ws/notes.md")
    with self.assertRaises(FileNotFoundError):
      self.under("B", lambda: os.listdir(note.parent))
    self.assertEqual(self.under("A", lambda: os.listdir(note.parent)), ["notes.md"])

  def test_os_open_flags(self):
    path = self.root / "x.txt"
    def write():
      fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
      os.write(fd, b"alice")
      os.close(fd)
    self.under("A", write)
    with self.assertRaises(FileNotFoundError):
      self.under("B", lambda: os.close(os.open(path, os.O_RDONLY)))
    self.under("B", write)  # a truncating write reads nothing, and relabels
    self.assertEqual(self.mon.label("file:x.txt", ""), frozenset({"tools@B"}))

  def test_atomic_save_labels_target(self):
    target, tmp = self.root / "memory.json", self.root / "memory.tmp"
    self.under("A", lambda: (tmp.write_text("{}"), tmp.replace(target)))
    self.assertEqual(self.mon.label("file:memory.json", ""), frozenset({"tools@A"}))
    self.assertIsNone(self.mon.label("file:memory.tmp", ""))
    self.under("A", target.unlink)
    self.assertIsNone(self.mon.label("file:memory.json", ""))

  def test_flag_allows(self):
    mon = Monitor(Isolation(), "flag")
    note = self.root / "n.md"
    self.under("A", lambda: note.write_text("alice"), mon)
    self.assertEqual(self.under("B", note.read_text, mon), "alice")
    self.assertEqual(mon.violations[0].action, "flagged")

  def test_preexisting_file_unlabelled(self):
    (self.root / "old.md").write_text("x")
    self.assertEqual(self.under("B", (self.root / "old.md").read_text), "x")
    self.assertEqual(self.mon.stats.unlabelled, 1)

  def test_process_reported(self):
    self.under("A", lambda: subprocess.run(["true"], check=False))
    self.assertIn("subprocess.Popen", [u.event for u in self.mon.unseen])

  def test_outside_root_ignored(self):
    other = Path(tempfile.mkdtemp()) / "f"
    self.under("A", lambda: other.write_text("x"))
    self.assertEqual(self.under("B", other.read_text), "x")
    self.assertEqual(self.mon.labels, {})


class State(TypedDict, total=False):
  q: str
  secret: str
  out: str


@unittest.skipUnless(HAS_LANGGRAPH, "langgraph not installed")
class GraphTest(unittest.TestCase):
  def graph(self, mon, mode_check=None):
    from langgraph.checkpoint.memory import InMemorySaver
    from langgraph.graph import END, START, StateGraph

    def remember(s):
      return {"secret": s["q"]} if s.get("q", "").startswith("remember") else {}

    def answer(s):
      return {"out": f"answer to {s['q']} with {s.get('secret', '')!r}"}

    g = StateGraph(State)
    g.add_node("remember", remember)
    g.add_node("answer", answer)
    g.add_edge(START, "remember")
    g.add_conditional_edges("remember", lambda s: "answer" if s.get("q") else END)
    g.add_edge("answer", END)
    return monitor_graph(g, mon).compile(checkpointer=InMemorySaver())

  def go(self, mon, graph, principal, q):
    cfg = {"configurable": {"thread_id": "shared"}}
    with mon.serving(principal):
      mon.label_input("shared", {"q": q})
      return graph.invoke({"q": q}, cfg)

  def test_state_key_masked_across_principals(self):
    mon = Monitor(Isolation())
    g = self.graph(mon)
    self.go(mon, g, "A", "remember alice")
    out = self.go(mon, g, "B", "what?")
    self.assertEqual(out["out"], "answer to what? with ''")
    self.assertEqual(out["secret"], "remember alice")  # the host state keeps it, unshown
    self.assertEqual({(v.channel, v.agent, v.writers) for v in mon.violations},
                     {("secret", "answer@B", ("remember@A",))})
    out = self.go(mon, g, "A", "again")
    self.assertEqual(mon.label("secret", "shared"), frozenset({"remember@A"}))
    self.assertIn("remember alice", out["out"])

  def test_state_flag_and_raise(self):
    mon = Monitor(Isolation(), "flag")
    g = self.graph(mon)
    self.go(mon, g, "A", "remember alice")
    self.assertIn("alice", self.go(mon, g, "B", "what?")["out"])
    self.assertEqual(len(mon.violations), 1)
    mon = Monitor(Isolation(), "raise")
    g = self.graph(mon)
    self.go(mon, g, "A", "remember alice")
    with self.assertRaises(MonitorViolation):
      self.go(mon, g, "B", "what?")

  def test_unread_key_is_no_violation(self):
    mon = Monitor(Isolation())
    g = self.graph(mon)
    self.go(mon, g, "A", "remember alice")
    self.go(mon, g, "B", "")
    self.assertEqual(mon.violations, [])

  def test_async_node(self):
    from langgraph.checkpoint.memory import InMemorySaver
    from langgraph.graph import END, START, StateGraph

    async def leak(s):
      return {"out": s.get("secret", "")}
    g = StateGraph(State)
    g.add_node("leak", leak)
    g.add_edge(START, "leak")
    g.add_edge("leak", END)
    mon = Monitor(Isolation())
    graph = monitor_graph(g, mon).compile(checkpointer=InMemorySaver())
    cfg = {"configurable": {"thread_id": "t"}}

    async def go():
      with mon.serving("A"):
        mon.label_input("t", {"secret": "alice"})
        await graph.ainvoke({"secret": "alice"}, cfg)
      with mon.serving("B"):
        return await graph.ainvoke({}, cfg)
    self.assertEqual(asyncio.run(go())["out"], "")

  def test_store(self):
    mon = Monitor(Isolation())
    store = monitored_store(mon)
    with mon.serving("A"), mon.acting("w"):
      store.put(("mem",), "k", {"v": "alice"})
    with mon.serving("B"), mon.acting("r"):
      self.assertIsNone(store.get(("mem",), "k"))
      self.assertEqual(store.search(("mem",)), [])
      store.put(("mem",), "k", {"v": "bob"})
    with mon.serving("A"), mon.acting("r"):
      self.assertEqual(store.get(("mem",), "k").value, {"v": "alice"})
    self.assertEqual(len(mon.violations), 3)

  def test_built_prompt(self):
    mon = Monitor(Isolation(), "flag")
    from langgraph.graph import END, START, StateGraph
    g = StateGraph(State)
    g.add_node("model", lambda s: {"out": "x"})
    g.add_edge(START, "model")
    g.add_edge("model", END)
    graph = monitor_graph(g, mon, built_readers=("model",)).compile()
    with mon.serving("B"):
      with mon.acting("make_agent", principal="A"):  # a factory acting for the wrong user
        mon.built("built:agent", "prompt with alice")
      graph.invoke({"q": "hi"})
    self.assertEqual([(v.seam, v.agent) for v in mon.violations], [("built", "model@B")])
    mon.mode = "block"
    with mon.serving("B") as run, self.assertRaises(MonitorViolation):
      with mon.acting("make_agent", principal="A"):
        mon.built("built:agent", "prompt")
      del run
      graph.invoke({"q": "hi"})


if __name__ == "__main__":
  unittest.main()
