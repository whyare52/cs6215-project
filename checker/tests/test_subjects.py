"""Known leaks on the subject adapters, each run in its subject's venv as a subprocess.

A test skips when its subject repo or venv is missing (run `setup-case-studies.sh`).
"""

import functools
import json
import subprocess
import sys
import unittest
from pathlib import Path

PY_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PY_DIR))

from drivers import APPS_DIR, VENVS_DIR  # noqa: E402

MAIN_PYTHON = PY_DIR / ".venv" / "bin" / "python"
TRIAGE = "store:email_assistant/triage_preferences"
DRAFTS_A = "writer_messages#A/run0<-"
DOCS_A = "retrieved_documents#A/run0<-"
MEMORY = "ext:memory"


@functools.cache
def run(module: str, repo: str, venv: Path, *args: str) -> dict[str, dict]:
  """The adapter's summaries by name, or a skip when the subject is not set up."""
  python = venv / "bin" / "python"
  if not (APPS_DIR / repo).is_dir():
    raise unittest.SkipTest(f"subject repo missing: {APPS_DIR / repo}")
  if not python.exists():
    raise unittest.SkipTest(f"venv missing: {venv}")
  proc = subprocess.run([str(python), "-m", f"drivers.{module}", "--no-write", *args],
                        cwd=PY_DIR, capture_output=True, text=True, timeout=600)
  if proc.returncode:
    raise AssertionError(f"{module} failed:\n{proc.stdout[-2000:]}\n{proc.stderr[-4000:]}")
  line = next(ln for ln in proc.stdout.splitlines() if ln.startswith("LGTRACE_JSON "))
  return {s["name"]: s for s in json.loads(line.removeprefix("LGTRACE_JSON "))}


def flows(summary: dict) -> set[tuple[str, str, str]]:
  return {tuple(f) for f in summary["flows"]}


def boards_on(path: list[str]) -> list[str]:
  return [step.split(" via board ")[1] for step in path if " via board " in step]


def drafts_of_a(board: str) -> bool:
  """A board of A's drafts, written by a task serving A."""
  return board.startswith(DRAFTS_A) and board.endswith("@A")


class AgentsFromScratchTests(unittest.TestCase):
  """Lockfile versions (langgraph 0.4.8)."""

  def summary(self, *args: str) -> dict:
    return run("agents_from_scratch", "agents-from-scratch", VENVS_DIR / "agents-from-scratch",
               *args)["agents_from_scratch"]

  def test_ignored_email_reaches_next_triage_through_store(self):
    s = self.summary()
    self.assertTrue(boards_on(s["findings"]["triage_router@B"])[-1].startswith(f"{TRIAGE}#A<-"))
    self.assertIn(("A", TRIAGE, "triage_router@B"), flows(s))
    self.assertEqual((s["unattributed"], s["fallbacks"]), (0, []))

  def test_no_path_through_another_threads_messages(self):
    """Senders run in separate threads, so A's `messages` cannot reach a task of B."""
    s = self.summary()
    steps = [step for path in s["findings"].values() for step in path]
    self.assertFalse([st for st in steps if "@B via board messages#A/thread-A" in st])
    self.assertTrue(all(b.startswith("store:") for path in s["findings"].values()
                        for b in boards_on(path)[1:]))

  def test_notify_then_ignore_alone_leaks(self):
    s = self.summary("--where", "notify_human=ignore", "--where", "RouterSchema=notify")
    self.assertEqual(s["scripts"], 1)
    path = s["findings"]["triage_router@B"]
    self.assertIn("triage_interrupt_handler@A", path[1])
    self.assertIn(f"{TRIAGE}#A", path[-1])

  def test_triage_ignore_does_not_leak(self):
    s = self.summary("--where", "RouterSchema=ignore")
    self.assertEqual((s["findings"], s["flows"]), ({}, []))


class Kaymen99Tests(unittest.TestCase):
  """Venv resolved as of the subject commit (langgraph 0.2.72), and langgraph 1.2.24."""

  venv = VENVS_DIR / "kaymen99"

  def summaries(self, *args: str) -> dict[str, dict]:
    return run("kaymen99", "langgraph-email-automation", self.venv, *args)

  def test_drafts_reach_next_customer_writer(self):
    s = self.summaries()["kaymen99"]
    self.assertTrue(any(map(drafts_of_a, boards_on(s["findings"]["email_writer@B"]))))
    self.assertIn(("A", "writer_messages", "email_writer@B"), flows(s))
    self.assertIn(("A", "writer_messages", "email_proofreader@B"), flows(s))
    self.assertEqual((s["unattributed"], s["fallbacks"]), (0, []))

  def test_fix_findings_all_go_through_the_docs_leak(self):
    s = self.summaries()["kaymen99-fixed"]
    self.assertIn("email_writer@B", s["findings"])
    for victim, path in s["findings"].items():
      with self.subTest(victim=victim):
        self.assertFalse(any(map(drafts_of_a, boards_on(path))))
        self.assertTrue(any(b.startswith(DOCS_A) for b in boards_on(path)))

  def test_findings_separate_bug_from_fix_on_send_path(self):
    """A's docs leak only on the stop path, so on the send path only the bug has findings."""
    s = self.summaries("--where", "proof_A=send")
    self.assertIn("email_writer@B", s["kaymen99"]["findings"])
    self.assertEqual(s["kaymen99-fixed"]["findings"], {})

  def test_stop_leaves_trials_for_the_next_customer(self):
    """A's stop leaves `trials` at 3, so B's first draft is already its last. No marker shows
    it, and the read is reported beside the findings."""
    s = self.summaries("--where", "proof_A=stop")
    for name in ("kaymen99", "kaymen99-fixed"):
      self.assertIn(["A", "trials", "email_writer@B", "email_writer@A"], s[name]["cross_reads"])

  def test_drafts_leak_on_send_path_too(self):
    s = self.summaries("--where", "proof_A=send")["kaymen99"]
    self.assertIn(("A", "writer_messages", "email_writer@B"), flows(s))

  def test_remove_message_fix_stops_drafts_leak(self):
    s = self.summaries()["kaymen99-fixed"]
    self.assertNotIn(("A", "writer_messages", "email_writer@B"), flows(s))

  def test_docs_reach_complaint_reply_on_stop_path_only(self):
    stop = self.summaries("--where", "proof_A=stop", "--where", "category_A=product_enquiry",
                          "--where", "category_B=customer_complaint")
    send = self.summaries("--where", "proof_A=send")
    for name in ("kaymen99", "kaymen99-fixed"):
      self.assertIn(("A", "retrieved_documents", "email_writer@B"), flows(stop[name]))
      self.assertNotIn(("A", "retrieved_documents", "email_writer@B"), flows(send[name]))

  def test_stop_on_last_email_crashes(self):
    s = self.summaries("--where", "proof_A=send", "--where", "proof_B=stop")["kaymen99"]
    self.assertEqual(list(s["crashes"]),
                     ["IndexError at src/nodes.py:36: list index out of range"])


class DeerFlowTests(unittest.TestCase):
  """Pre-fix `00a90bb`, fix `2e05f38`, its completion `da174dfd` and `c0da2782`, which threads
  the user into the memory updater. Each version runs in its own process and venv."""

  repos = ("deer-flow", "deer-flow-2e05f38", "deer-flow-da174dfd", "deer-flow-fixed")
  venvs = ("deerflow", "deerflow-fixed")

  def summaries(self, *args: str) -> dict[str, dict]:
    for r in self.repos:
      if not (APPS_DIR / r).is_dir():
        raise unittest.SkipTest(f"subject repo missing: {APPS_DIR / r}")
    for v in self.venvs:
      if not (VENVS_DIR / v / "bin" / "python").exists():
        raise unittest.SkipTest(f"venv missing: {VENVS_DIR / v}")
    venv = VENVS_DIR / ("deerflow-fixed" if "fixed" in args or "completed" in args
                        else "deerflow")
    return run("deerflow", self.repos[0], venv, *args)

  def test_a_reaches_b_lead_agent_through_shared_memory(self):
    s = self.summaries()["deerflow"]
    boards = boards_on(s["findings"]["model@B"])
    self.assertEqual(boards[1:], [f"{MEMORY}#A<-memory_updater@A",
                                  "built:lead_agent#A<-make_lead_agent@B"])
    self.assertIn(("A", MEMORY, "make_lead_agent@B"), flows(s))
    self.assertEqual((s["unattributed"], s["fallbacks"], s["crashes"]), (0, [], {}))

  def test_fix_as_committed_crashes_every_run(self):
    s = self.summaries()["deerflow-2e05f38"]
    self.assertEqual(list(s["crashes"]), ["TypeError at memory/queue.py:69: MemoryUpdateQueue."
                                          "_enqueue_locked() got an unexpected keyword argument "
                                          "'user_id'"])

  def test_completion_leaves_the_updater_on_the_shared_file(self):
    """At `da174dfd` lead agents read per-user memory, but the updater drops `user_id`, so it
    reads and writes the legacy shared file. No lead agent of B is reached, B's updater is,
    and no lead agent ever reads a marker from memory."""
    s = self.summaries()["deerflow-da174dfd"]
    self.assertEqual(list(s["findings"]), ["memory_updater@B"])
    self.assertEqual(boards_on(s["findings"]["memory_updater@B"])[-1],
                     f"{MEMORY}#A<-memory_updater@A")
    self.assertFalse([r for r in s["shared_reads"] if r[2].startswith("make_lead_agent@")])

  def test_fix_has_no_findings_and_memory_still_reaches_its_own_user(self):
    s = self.summaries()["deerflow-fixed"]
    self.assertEqual((s["findings"], s["unexplained"], s["crashes"]), ({}, [], {}))
    self.assertIn(["A", MEMORY, "make_lead_agent@A"], s["shared_reads"])
    self.assertIn(["A", "built:lead_agent", "model@A"], s["shared_reads"])

  def test_dropped_updates_do_not_leak_before_the_fix(self):
    """A fact under the confidence threshold and a reply with nothing to store leave no marker
    in memory, though the fake LLM's reply carries one."""
    for choice in ("low", "none"):
      with self.subTest(memory=choice):
        s = self.summaries("--version", "pre", "--where", f"memory={choice}")["deerflow"]
        self.assertEqual(s["findings"], {})

  def test_file_seam_alone_misses_the_cached_load(self):
    """B's load is served from `FileMemoryStorage`'s cache and opens no file, so without the
    storage seam there is no finding, and the markers report the flow as unexplained."""
    s = self.summaries("--version", "pre", "--seams", "file", "--where", "memory=fact",
                       "--where", "lead=reply")["deerflow-file"]
    self.assertEqual(s["findings"], {})
    self.assertIn(["A", "built:lead_agent", "model@B"], s["unexplained"])


class OpenDeepResearchTests(unittest.TestCase):
  """Lockfile versions (langgraph 1.2.9). No known cross-user bug, so a precision check."""

  def summary(self, *args: str) -> dict:
    return run("open_deep_research", "open_deep_research", VENVS_DIR / "open-deep-research",
               *args)["open_deep_research"]

  def test_no_finding_across_users(self):
    s = self.summary()
    self.assertEqual(s["scripts"], 14)
    self.assertEqual((s["findings"], s["flows"], s["unexplained"], s["cross_reads"]),
                     ({}, [], [], []))
    self.assertEqual((s["unattributed"], s["fallbacks"]), (0, []))


class AgentServiceToolkitTests(unittest.TestCase):
  """Pre-fix `6aabc5e`, #305 `54d5e89`, PR #355's metadata check `1a1da86` and #355 as merged
  `a561c88`, each in its own process, on one venv."""

  repos = ("agent-service-toolkit", "agent-service-toolkit-54d5e89",
           "agent-service-toolkit-1a1da86", "agent-service-toolkit-a561c88")
  victims = ["guard_input@B", "model@B", "tools@B"]

  def summaries(self, *args: str) -> dict[str, dict]:
    for r in self.repos:
      if not (APPS_DIR / r).is_dir():
        raise unittest.SkipTest(f"subject repo missing: {APPS_DIR / r}")
    return run("agent_service_toolkit", self.repos[0], VENVS_DIR / "agent-service-toolkit",
               *args)

  def test_post_into_anothers_thread_reaches_owner(self):
    s = self.summaries()["agent_service_toolkit"]
    self.assertEqual(sorted(s["findings"]), self.victims)
    self.assertEqual(boards_on(s["findings"]["model@B"])[-1], "messages#A/thread-B<-model@A")
    self.assertEqual((s["unexplained"], s["unattributed"], s["fallbacks"]), ([], 0, []))

  def test_check_on_state_config_never_fires(self):
    s = self.summaries()["agent_service_toolkit-54d5e89"]
    self.assertEqual(sorted(s["findings"]), self.victims)
    self.assertEqual(s["refused"], {})

  def test_metadata_check_refuses_own_id_and_fresh_id_but_not_spoof(self):
    s = self.summaries()["agent_service_toolkit-1a1da86"]
    self.assertEqual(sorted(s["findings"]), self.victims)
    self.assertEqual(s["refused"], {"403 for post 1": 6})
    for as_user, leaks in (("own", False), ("none", False), ("victim", True)):
      with self.subTest(as_user=as_user):
        one = self.summaries("--version", "metadata", "--where", f"as_user={as_user}")
        self.assertEqual(bool(one["agent_service_toolkit-1a1da86"]["findings"]), leaks)

  def test_reverted_check_leaks_again(self):
    s = self.summaries()["agent_service_toolkit-a561c88"]
    self.assertEqual(sorted(s["findings"]), self.victims)


class YuxiTests(unittest.TestCase):
  """Pre-fix `db0dcb0d` and fix `e0c6159c` (#594), each in its own process, on one venv."""

  def summaries(self, *args: str) -> dict[str, dict]:
    if not (APPS_DIR / "Yuxi-fixed").is_dir():
      raise unittest.SkipTest(f"subject repo missing: {APPS_DIR / 'Yuxi-fixed'}")
    return run("yuxi", "Yuxi", VENVS_DIR / "yuxi", *args)

  def test_a_note_reaches_b_through_the_shared_workspace(self):
    s = self.summaries()["yuxi"]
    self.assertEqual(sorted(s["findings"]), ["model@B", "tools@B"])
    self.assertEqual(boards_on(s["findings"]["tools@B"])[-1],
                     "file:threads/shared/workspace/notes.md#A<-tools@A")
    self.assertEqual((s["unexplained"], s["unattributed"], s["fallbacks"]), ([], 0, []))

  def test_fix_keeps_the_note_with_its_user(self):
    s = self.summaries()["yuxi-fixed"]
    self.assertEqual((s["findings"], s["flows"], s["unexplained"]), ({}, [], []))
    self.assertEqual(s["shared_reads"],
                     [["A", "file:threads/shared/A/workspace/notes.md", "tools@A"]])

  def test_no_leak_unless_a_writes_and_b_reads(self):
    s = self.summaries("--version", "pre", "--where", "tool_B=reply")["yuxi"]
    self.assertEqual(s["findings"], {})


class ExecutiveAIAssistantTests(unittest.TestCase):
  """`758db71` with langgraph 0.5.4 (the lockfile's 0.5.0 does not import with its own
  langchain-core). No upstream issue, so the findings are code-evident paths only."""

  def summary(self, *args: str) -> dict:
    return run("executive_ai_assistant", "executive-ai-assistant",
               VENVS_DIR / "executive-ai-assistant", *args)["executive_ai_assistant"]

  def test_ignored_email_reaches_next_triage_as_few_shot_example(self):
    s = self.summary("--where", "triage=email", "--where", "tool=Question",
                     "--where", "tool_human=ignore")
    self.assertEqual(list(s["findings"]), ["triage_input@B"])
    self.assertEqual(boards_on(s["findings"]["triage_input@B"])[-1],
                     "store:default/triage_examples#A")

  def test_reflection_carries_the_email_into_b_draft(self):
    s = self.summary("--where", "triage=email", "--where", "tool=ResponseEmailDraft",
                     "--where", "tool_human=response", "--where", "reflect=all")
    self.assertIn("store:default#A<-send_email_draft/reflection/update_general@A",
                  boards_on(s["findings"]["draft_response@B"]))

  def test_triage_no_saves_nothing(self):
    s = self.summary("--where", "triage=no")
    self.assertEqual((s["findings"], s["flows"]), ({}, []))

  def test_whole_run_is_attributed(self):
    s = self.summary()
    self.assertEqual((s["unexplained"], s["unattributed"], s["fallbacks"]), ([], 0, []))


class AegraTests(unittest.TestCase):
  """Pre-fix `9438b502` and fix `f1f75177` (#275, #276), each in its own venv."""

  def summaries(self, *args: str) -> dict[str, dict]:
    for r, v in (("aegra-fixed", "aegra-fixed"),):
      if not (APPS_DIR / r).is_dir() or not (VENVS_DIR / v / "bin" / "python").exists():
        raise unittest.SkipTest(f"subject or venv missing: {r}")
    return run("aegra", "aegra", VENVS_DIR / "aegra", *args)

  def test_put_into_b_namespace_reaches_b_graph(self):
    s = self.summaries()["aegra"]
    self.assertEqual(sorted(s["findings"]), ["answer@B", "my_node@B"])
    self.assertEqual(boards_on(s["findings"]["my_node@B"]),
                     ["in#A", "store:users/B/preferences#A"])
    self.assertEqual((s["unexplained"], s["unattributed"], s["fallbacks"]), ([], 0, []))

  def test_fix_scopes_the_put_under_its_caller(self):
    s = self.summaries()["aegra-fixed"]
    self.assertEqual((s["findings"], s["flows"], s["unexplained"]), ({}, [], []))
    self.assertIn(["A", "store:users/A/preferences", "my_node@A"], s["shared_reads"])


class AegraThreadsTests(unittest.TestCase):
  """Pre-fix `d7d80c85` and fix `e1b20422` (#336, #337) on a live Postgres at `AEGRA_PG`."""

  def summaries(self) -> dict[str, dict]:
    import os
    import socket
    from urllib.parse import urlsplit
    for r in ("aegra-d7d80c85", "aegra-e1b2042"):
      if not (APPS_DIR / r).is_dir() or not (VENVS_DIR / r / "bin" / "python").exists():
        raise unittest.SkipTest(f"subject or venv missing: {r}")
    url = urlsplit(os.environ.get("AEGRA_PG", "postgresql://user:password@127.0.0.1:55432"))
    try:
      socket.create_connection((url.hostname, url.port or 5432), timeout=2).close()
    except OSError:
      raise unittest.SkipTest(f"no Postgres at {url.hostname}:{url.port}") from None
    return run("aegra_threads", "aegra-d7d80c85", VENVS_DIR / "aegra-d7d80c85")

  def test_run_on_b_thread_reaches_b_next_turn(self):
    s = self.summaries()["aegra_threads"]
    self.assertEqual(sorted(s["findings"]), ["call_model@B"])
    self.assertEqual(boards_on(s["findings"]["call_model@B"]),
                     ["in#A", "messages#A/thread-B<-call_model@A"])
    self.assertEqual(s["http"][1], ["A", "thread-B", 200])
    self.assertEqual((s["unexplained"], s["unattributed"], s["fallbacks"]), ([], 0, []))

  def test_fix_refuses_the_foreign_run(self):
    s = self.summaries()["aegra_threads-fixed"]
    self.assertEqual((s["findings"], s["flows"], s["unexplained"]), ({}, [], []))
    self.assertEqual(s["http"][1], ["A", "thread-B", 404])


class AixDbTests(unittest.TestCase):
  """`ac8e14b1`, the same with the fix's schema line, and fix `fa9ee98b`. B holds the secret."""

  def summaries(self, *args: str) -> dict[str, dict]:
    if not (APPS_DIR / "Aix-DB-fixed").is_dir():
      raise unittest.SkipTest("subject repo missing: Aix-DB-fixed")
    return run("aix_db", "Aix-DB", VENVS_DIR / "aix-db", *args)

  def test_shared_duckdb_gives_b_rows_to_a(self):
    s = self.summaries()
    self.assertEqual(s["aix_db"]["findings"], {})  # pre registers no table at all
    found = s["aix_db-schema"]["findings"]
    self.assertEqual(sorted(found), ["data_render_apache@A", "sql_executor@A",
                                     "sql_generator@A", "summarize@A"])
    self.assertEqual(boards_on(found["sql_executor@A"]),
                     ["in#B", "duckdb:0#B<-excel_parsing@B"])
    fixed = s["aix_db-fixed"]
    self.assertEqual((fixed["findings"], fixed["flows"], fixed["unexplained"]), ({}, [], []))
    self.assertIn(["A", "duckdb:1", "sql_executor@A"], fixed["shared_reads"])


class Kaymen99LatestTests(Kaymen99Tests):
  """The same assertions on lgtrace's own venv (langgraph 1.2.24)."""

  venv = MAIN_PYTHON.parents[1]


if __name__ == "__main__":
  unittest.main()
