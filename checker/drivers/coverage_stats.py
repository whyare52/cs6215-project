"""Coverage of one subject version's traced runs.

Run in the subject's venv from `project/checker`, as
`../case-studies/venvs/yuxi/bin/python -m drivers.coverage_stats yuxi pre`. Prints one JSON line
- `nodes`, the graph nodes of every graph the adapter instrumented, and `ran`, those some
  traced task executed. Start and end are not counted.
- `app_statements` and `app_executed`, Python statements under the app's source root and those
  the traced runs executed, by coverage.py, tests excluded.
- `scripts`, the fake-LLM scripts, one per combination of the adapter's scripted choices.
- `adapter_loc`, non-blank lines of the adapter module.
The spec is not written.
"""

from __future__ import annotations

import contextlib
import importlib
import io
import json
import sys
from pathlib import Path
from typing import Any

import coverage

import lgtrace
from drivers import repo

# The app source each adapter exercises, relative to its repo
SOURCES = {
  "deerflow": "backend", "yuxi": "backend", "aegra": "libs/aegra-api/src", "aix_db": ".",
}
TEST_PARTS = ("test", "tests", "testing")


def graph_nodes(builder: Any) -> set[str]:
  return {n for n in builder.nodes if n not in ("__start__", "__end__")}


def main() -> None:
  name, version = sys.argv[1], sys.argv[2]
  module = importlib.import_module(f"drivers.{name}")
  root = repo(module.REPOS[version]) / SOURCES[name]
  nodes: set[str] = set()
  traces: list[Any] = []
  instrument, trace_subject = lgtrace.instrument, lgtrace.trace_subject

  def recording_instrument(builder: Any) -> Any:
    nodes.update(graph_nodes(builder))
    return instrument(builder)

  def recording_trace(subject: Any) -> Any:
    trace = trace_subject(subject)
    traces.append((subject, trace))
    return trace
  lgtrace.instrument = recording_instrument
  lgtrace.trace_subject = recording_trace
  omit = [f"*/{p}/*" for p in TEST_PARTS] + ["*/test_*.py", "*_test.py"]
  cov = coverage.Coverage(source=[str(root)], omit=omit, data_file=None)
  cov.start()
  with contextlib.redirect_stdout(io.StringIO()):
    if name == "deerflow":
      module.one(version, module.SEAMS, ["--no-write"])
    else:
      module.one(version, ["--no-write"])
  cov.stop()
  subject, trace = traces[-1]
  ran = {a.node for a in trace.accesses} & nodes
  analysed = [cov.analysis2(f) for f in cov.get_data().measured_files()]
  executed = sum(len(stmts) - len(missing) for _, stmts, _, missing, _ in analysed)
  with contextlib.redirect_stdout(io.StringIO()):
    total = cov.report(file=io.StringIO())
  statements = sum(len(stmts) for _, stmts, _, _, _ in analysed)
  adapter = Path(module.__file__ or "")
  print(json.dumps({
    "subject": name, "version": version, "nodes": sorted(nodes), "ran": sorted(ran),
    "missed": sorted(nodes - ran), "scripts": len(subject.scripts),
    "runs": len(subject.runs), "app_files_imported": len(analysed),
    "app_statements_imported": statements, "app_executed": executed,
    "percent_of_imported": round(total, 1),
    "adapter_loc": sum(1 for line in adapter.read_text().splitlines() if line.strip()),
  }))


if __name__ == "__main__":
  main()
