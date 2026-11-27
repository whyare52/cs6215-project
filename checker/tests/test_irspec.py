import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from irspec import explain, from_dict, leaks, load, reach  # noqa: E402
from lean_export import to_lean  # noqa: E402

IR_ROOT = Path(__file__).resolve().parents[2] / "proofs"
SPECS = Path(__file__).resolve().parent / "fixtures"


def tiny(**overrides):
  base = {
    "agents": ["A", "B"],
    "boards": {},
    "owner": {"vA": "A", "vB": "B"},
    "sees": "own",
    "echo_sees": "none",
    "adversary": {"controls": ["B"]},
  }
  return from_dict({**base, **overrides})


class ReachTests(unittest.TestCase):
  def test_terrarium_reaches_everyone(self):
    self.assertEqual(reach(load(SPECS / "meeting_terrarium.json")),
                     {"Alice", "Bob", "Carol", "Mallory"})

  def test_hardened_isolates_alice_and_bob(self):
    self.assertEqual(reach(load(SPECS / "meeting_hardened.json")), {"Carol", "Mallory"})

  def test_leaks_match_lean_examples(self):
    self.assertEqual(leaks(load(SPECS / "meeting_terrarium.json"), ["Alice"]), {"Mallory"})
    self.assertEqual(leaks(load(SPECS / "meeting_hardened.json"), ["Alice"]), frozenset())

  def test_no_flow_without_edges(self):
    self.assertEqual(reach(tiny()), {"B"})

  def test_board_edge(self):
    self.assertEqual(reach(tiny(boards={"b": ["A", "B"]})), {"A", "B"})

  def test_sees_edge(self):
    self.assertEqual(reach(tiny(sees={"A": ["vB"]})), {"A", "B"})

  def test_sees_is_directed(self):
    self.assertEqual(reach(tiny(sees={"B": ["vA"]})), {"B"})

  def test_echo_edge_needs_an_owner_on_the_board(self):
    self.assertEqual(reach(tiny(boards={"b": ["A"]}, echo_sees="all")), {"A", "B"})

  def test_echo_edge_needs_echoed_variable(self):
    self.assertEqual(reach(tiny(boards={"b": ["A"]}, echo_sees=["vA"])), {"B"})

  def test_injection(self):
    spec = tiny(boards={"b": ["A"]}, adversary={"controls": [], "injects": ["b"]})
    self.assertEqual(reach(spec), {"A"})

  def test_explain_gives_a_path(self):
    path = explain(load(SPECS / "meeting_terrarium.json"))["Alice"]
    self.assertEqual(path[0], "controlled Mallory")
    self.assertIn("Mallory -> Alice", path[-1])

  def test_validate_rejects_unknown_names(self):
    with self.assertRaises(ValueError):
      tiny(boards={"b": ["Z"]})
    with self.assertRaises(ValueError):
      tiny(adversary={"controls": ["Z"]})

  def test_board_roles_direct_the_edge(self):
    roles = {"b": {"readers": ["A"], "writers": ["B"]}}
    self.assertEqual(reach(tiny(boards=roles)), {"A", "B"})
    roles = {"b": {"readers": ["B"], "writers": ["A"]}}
    self.assertEqual(reach(tiny(boards=roles)), {"B"})

  def test_member_list_means_read_and_write(self):
    spec = tiny(boards={"b": ["A", "B"]})
    self.assertEqual(spec.readers_of("b"), {"A", "B"})
    self.assertEqual(spec.writers_of("b"), {"A", "B"})
    self.assertEqual(spec.boards["b"], {"A", "B"})

  def test_missing_role_means_nobody(self):
    spec = tiny(boards={"b": {"writers": ["B"]}})
    self.assertEqual(spec.readers_of("b"), frozenset())
    self.assertEqual(reach(spec), {"B"})

  def test_echo_goes_from_owner_writers_to_readers(self):
    roles = {"b": {"readers": ["B"], "writers": ["A"]}}
    self.assertEqual(reach(tiny(boards=roles, echo_sees="all")), {"B"})
    roles = {"b": {"readers": ["A"], "writers": ["B"]}}
    self.assertEqual(reach(tiny(boards=roles, echo_sees="all")), {"A", "B"})

  def test_injection_reaches_readers_only(self):
    spec = tiny(boards={"b": {"readers": ["A"], "writers": ["B"]}},
                adversary={"controls": [], "injects": ["b"]})
    self.assertEqual(reach(spec), {"A"})

  def test_validate_rejects_bad_roles(self):
    with self.assertRaises(ValueError):
      tiny(boards={"b": {"readers": ["Z"]}})
    with self.assertRaises(ValueError):
      tiny(boards={"b": {"members": ["A"]}})

  def test_empty_spec(self):
    spec = from_dict({"agents": ["A"], "boards": {}, "owner": {}})
    self.assertEqual(reach(spec), frozenset())


@unittest.skipUnless(shutil.which("lake"), "needs Lean")
class LeanExportTests(unittest.TestCase):
  def check(self, spec_name: str) -> str:
    return self.compile(to_lean(load(SPECS / spec_name), "GeneratedTest"))

  def compile(self, source: str) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=IR_ROOT, delete=False) as f:
      f.write(source)
      path = Path(f.name)
    try:
      result = subprocess.run(["lake", "env", "lean", str(path)], cwd=IR_ROOT,
                              capture_output=True, text=True, timeout=600)
    finally:
      path.unlink()
    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
    return source

  def test_hardened_certificate_checks(self):
    source = self.check("meeting_hardened.json")
    self.assertIn("theorem safe_Alice", source)
    self.assertIn("theorem safe_Bob", source)
    self.assertNotIn("theorem safe_Mallory", source)

  def test_roles_certificate_checks(self):
    spec = tiny(boards={"b": {"readers": ["B"], "writers": ["A"]}})
    source = self.compile(to_lean(spec, "GeneratedRoles"))
    self.assertIn("theorem safe_A", source)
    self.assertNotIn("theorem safe_B", source)

  def test_terrarium_certificate_checks(self):
    source = self.check("meeting_terrarium.json")
    self.assertNotIn("theorem safe_", source)


if __name__ == "__main__":
  unittest.main()
