"""lgtrace adapter for apconw/Aix-DB, the shared DuckDB of table Q&A (fix fa9ee98b).

Aix-DB is a chat-with-your-data web app. A user uploads a spreadsheet or CSV and asks questions
about it in a chat, and the app answers with SQL over the file, a written summary and a chart.
Actors
- the users A and B, humans, each uploading a file to a chat of their own and asking about it.
  Here B uploads a payroll file, the secret, and A is the one who may read it.
- the table Q&A graph (`agent/excel/excel_graph.py`). `excel_parsing`, plain code, loads the
  chat's files into DuckDB. `sql_generator`, an LLM agent, writes SQL for the question.
  `sql_executor`, plain code, runs it. `summarize`, an LLM agent, writes the answer, and
  `data_render_apache`, plain code, builds the table.
- `ExcelDuckDBManager` (`agent/excel/excel_duckdb_manager.py`), plain code holding one DuckDB
  connection with a schema per uploaded file.

Before the fix `get_duckdb_manager()` returns one process-wide manager, so every chat's files
are tables in one database and A's SQL can name B's table. The fix, "implement chat_id-level
DuckDB session management" (fa9ee98b), gives each `chat_id` its own manager. Versions
- `pre`, `ac8e14b1` (the fix's parent), checkout `Aix-DB`.
- `pre-schema`, `ac8e14b1` with the one line of the fix that creates each file's schema
  (`CREATE SCHEMA IF NOT EXISTS <catalog>`, `excel_duckdb_manager.py:110` at the fix). Without
  it `pre` cannot register any table ("Schema with name ... does not exist"), so no file data
  is ever shared. This version isolates the other half of the fix, the per-chat manager.
- `fixed`, `fa9ee98b`, worktree `Aix-DB-fixed`.
Both are the same top-level packages (`agent`, `common`), so each runs in its own process, on
one venv `aix-db` with the app's locked versions of what the graph imports.

This is a confidentiality bug, so B is the marker source the checker follows (`ATTACKERS`). A
finding is a task of A that B's payroll marker reaches.

What runs. The real graph, nodes and DuckDB manager. Stubs
- MinIO, the object store behind uploads. `MinioUtils.get_file_url_by_key` returns the local
  path of the uploaded file, and the upload itself is external task `upload_file` of the run's
  user, which writes the file under `lgtrace.FileRecorder`.
- `get_llm` in the SQL and summary nodes returns `marker_llm`. The SQL is scripted, A's names
  A's own table or B's (`sql_A`), as a user asking for "the payroll table" would get.
- `ExcelDuckDBManager._get_connection` opens the in-memory database without loading the httpfs
  extension, which is only for remote files and needs a download.
- DuckDB is native code, so file and store recorders do not see it. Each manager's
  registrations and queries are recorded at its own interface as resource `duckdb:<n>`, `n`
  counting managers in the order a script creates them.
The antv chart node, which calls an MCP chart server, is never reached, since the scripted
chart type is the table one.
"""

from __future__ import annotations

import argparse
import functools
import json
import os
import shutil
import subprocess
import sys
import tempfile
import types
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from drivers import PY_DIR, VENVS_DIR, emit_json, on_path, options, report, repo
import lgtrace
from lgtrace import Run, Script, Subject, make_markers, marker_llm, router_scripts

NAME = "aix_db"
VENV = "aix-db"
REPOS = {"pre": "Aix-DB", "pre-schema": "Aix-DB", "fixed": "Aix-DB-fixed"}
NAMES = {"pre": NAME, "pre-schema": f"{NAME}-schema", "fixed": f"{NAME}-fixed"}
PRINCIPALS = ("A", "B")
ATTACKERS = frozenset({"B"})
FILES = {"A": "sales.csv", "B": "payroll.csv"}
TABLES = {"A": "sales.sales", "B": "payroll.payroll"}
CHOICES = {"sql_A": ("own", "other")}


def scripts() -> tuple[dict[str, str], ...]:
  return router_scripts(CHOICES)


@dataclass
class Current:
  markers: Mapping[str, str]
  script: Script
  user: str = ""
  managers: dict[int, str] = field(default_factory=dict)


CURRENT = Current({}, {})


def sql_llm() -> Any:
  """The SQL node's model. Its JSON answer names a table by the script, and carries the markers
  it saw in a field the node ignores."""
  user = CURRENT.user
  table = TABLES[user if CURRENT.script.get(f"sql_{user}", "own") == "own" else
                 next(p for p in PRINCIPALS if p != user)]
  text = json.dumps({"sql_query": f"SELECT * FROM {table}", "chart_type": "generate_table",
                     "seen": "{markers}"})
  return marker_llm(CURRENT.markers, {"text": text})


def summary_llm() -> Any:
  return marker_llm(CURRENT.markers, {"text": "Summary {markers}"})


def channel(manager: Any) -> str:
  return CURRENT.managers.setdefault(id(manager), f"duckdb:{len(CURRENT.managers)}")


@functools.cache
def subject_modules(version: str, upload_dir: str) -> types.SimpleNamespace:
  if "agent" in sys.modules:
    loaded = sys.modules["agent"].__file__ or ""
    if REPOS[version] not in Path(loaded).parts or "agent.excel" in sys.modules:
      raise RuntimeError(f"agent already imported from {loaded}, run each version alone")
  root = repo(REPOS[version])
  on_path(root)
  minio = types.ModuleType("common.minio_util")

  class MinioUtils:
    def get_file_url_by_key(self, bucket_name: str = "filedata",
                            object_key: str | None = None) -> str:
      return str(Path(upload_dir) / str(object_key))
  minio.MinioUtils = MinioUtils  # type: ignore[attr-defined]
  sys.modules["common.minio_util"] = minio
  import duckdb
  import agent.excel.excel_duckdb_manager as dm
  import agent.excel.excel_graph as eg
  import agent.excel.excel_sql_node as sql_node
  import agent.text2sql.analysis.llm_summarizer as summarizer
  sql_node.get_llm = sql_llm
  summarizer.get_llm = summary_llm
  cls = dm.ExcelDuckDBManager

  def connect(self: Any) -> Any:
    if self._connection is None:
      self._connection = duckdb.connect(database=":memory:")
    return self._connection
  cls._get_connection = connect
  if version == "pre-schema":
    register = cls._register_dataframes_to_catalog

    def with_schema(self: Any, dataframes: Any, catalog_name: str, file_name: str) -> Any:
      self._get_connection().execute(f"CREATE SCHEMA IF NOT EXISTS {catalog_name}")
      return register(self, dataframes, catalog_name, file_name)
    cls._register_dataframes_to_catalog = with_schema
  cls._register_dataframes_to_catalog = lgtrace.recorded(
    cls._register_dataframes_to_catalog, "write", lambda self, *a, **k: channel(self),
    lambda args, kwargs, result: [df.to_dict("records") for _, df in args[1]])
  cls.execute_sql = lgtrace.recorded(cls.execute_sql, "read",
                                     lambda self, *a, **k: channel(self))
  return types.SimpleNamespace(dm=dm, graph=eg)


def reset(mods: types.SimpleNamespace) -> None:
  """A fresh process state per script, as after a restart."""
  dm = mods.dm
  for name in ("_duckdb_manager", "_chat_duckdb_manager"):
    if hasattr(dm, name):
      setattr(dm, name, None)
  if hasattr(dm, "get_default_duckdb_manager"):
    vars(dm.get_default_duckdb_manager).pop("_default_manager", None)
  CURRENT.managers.clear()


@dataclass
class Server:
  """One script's server. A run's `upload` is the user's file upload, external task
  `upload_file` of the run's user, which reads the request body as resource `http:upload` and
  writes the file. The rest of the input is the chat turn, run through the graph."""
  graph: Any
  upload_dir: str

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    CURRENT.user = config["configurable"]["user"]
    upload = inp["upload"]
    turn = {k: v for k, v in inp.items() if k != "upload"}
    with lgtrace.FileRecorder(self.upload_dir):
      with lgtrace.acting("upload_file", parent=None):
        lgtrace.emit("http:upload", "read", upload)
        path = Path(self.upload_dir) / upload["key"]
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w") as f:
          f.write(upload["content"])
      events = list(self.graph.stream(turn, config, **kwargs))
    yield from events


def build(version: str, markers: Mapping[str, str]) -> Callable[[Any, Script], Any]:
  def go(store: Any, script: Script) -> Any:
    upload_dir = os.environ.setdefault("LGTRACE_AIXDB_UPLOADS",
                                       tempfile.mkdtemp(prefix="lgtrace-aixdb-"))
    mods = subject_modules(version, upload_dir)
    shutil.rmtree(Path(upload_dir) / "uploads", ignore_errors=True)
    reset(mods)
    CURRENT.markers, CURRENT.script = markers, script
    return Server(lgtrace.instrument_compiled(mods.graph.create_excel_graph()), upload_dir)
  return go


def make_subject(version: str) -> Subject:
  markers = make_markers(PRINCIPALS)
  rows = {"A": f"region,amount\nnorth,{markers['A']}\n",
          "B": f"name,salary\nbob,{markers['B']}\n"}
  runs = tuple(
    Run({"upload": {"key": f"uploads/{p}/{FILES[p]}", "content": rows[p]},
         "user_query": f"Show me the table. {markers[p]}",
         "file_list": [{"source_file_key": f"uploads/{p}/{FILES[p]}"}],
         "chat_id": f"chat-{p}"},
        p, {"configurable": {"thread_id": f"chat-{p}", "user": p}})
    for p in ("B", "A"))
  return Subject(build(version, markers), runs, markers, ATTACKERS, scripts())


def one(version: str, rest: list[str]) -> None:
  opts = options(rest)
  emit_json([report(NAMES[version], opts.narrow(make_subject(version)), opts.write)])


def main() -> None:
  ap = argparse.ArgumentParser()
  ap.add_argument("--version", choices=tuple(REPOS), help="one version, in this process")
  args, rest = ap.parse_known_args()
  if args.version:
    one(args.version, rest)
    return
  summaries = []
  for version in REPOS:
    proc = subprocess.run([str(VENVS_DIR / VENV / "bin" / "python"), "-m", "drivers.aix_db",
                           "--version", version, *rest], cwd=PY_DIR, capture_output=True,
                          text=True)
    print("".join(ln + "\n" for ln in proc.stdout.splitlines()
                  if not ln.startswith("LGTRACE_JSON ")), end="")
    if proc.returncode:
      print(proc.stderr[-4000:], file=sys.stderr)
      raise SystemExit(proc.returncode)
    line = next(ln for ln in proc.stdout.splitlines() if ln.startswith("LGTRACE_JSON "))
    summaries.extend(json.loads(line.removeprefix("LGTRACE_JSON ")))
  emit_json(summaries)


if __name__ == "__main__":
  main()
