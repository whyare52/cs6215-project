"""Generic seams for state an app shares outside LangGraph, the catalogue `lgauto` installs.

A Python app can share state across principals in finitely many ways. Each mechanism has one
generic seam here, recorded as `lgtrace` resource ops on a channel named by the mechanism.

| Mechanism | Channel | Seam |
| --- | --- | --- |
| 1 framework channels | state keys, `store:` | `lgtrace.instrument`, `RecordingStore` |
| 2 process memory | `mem:<module>.<name>` | `MemoryWatch`, a scan of app globals |
| 3 filesystem | `file:<path>` | `lgtrace.FileRecorder` (audit hooks) |
| 4 embedded databases | `db:<engine><n>/<table>` | `install_db`, sqlite3 and duckdb |
| 5 network services | `http:<host><path>` | `install_http`, a recording fake service |
| 6 build-time state | `built:<graph>`, `mem:` | prompt-text matching (`MemoryWatch.read`) |
| 7 carriers | none, attribution only | `install_carriers`, threads, pools, queues |

Process memory. `MemoryWatch.scan` walks the module globals and class attributes of every
module under the app's root, bounded, and collects the lines of their strings that carry a
marker. A line that appears in a global since the last scan is a write of `mem:<path>` by the
current task. A task reads `mem:<path>` when a marker-carrying line of its current value
occurs in what the task produced, an LLM prompt, a tool input, a node result or a graph a
factory built, which is the `built_reads` rule of `lgtrace` applied to every global. What it
cannot see: `functools.lru_cache` contents, native memory (a DuckDB table, a numpy buffer) and
objects reachable only from closures or locals of a running coroutine.

Embedded databases. `sqlite3.connect` gets a recording connection class, and `duckdb.connect`
returns a recording proxy. A statement's tables are read from its SQL. A read records the rows
the same statement returns, run first on a separate cursor, and a write records the rows of
each table it wrote, up to `DB_ROWS`. Each connection is its own database `<engine><n>`, `n`
counting connections, unless it names a file, which then names the database. Client-server
databases (psycopg, redis) reach the network guard and fail.

Network services. `http.client` (and with it urllib, urllib3, requests and minio), httpx's
default transports and aiohttp never open a socket. `FakeService` answers each request: a
`PUT`, `POST` or `PATCH` stores its body under host and path and is a write, a `GET` or
`HEAD` returns the body stored there, else a JSON stub with the markers of the request, and
is a read. aiohttp requests are recorded and then refused.

Carriers. A `threading.Thread` (and `Timer`) runs in the context of the code that started it,
a `ThreadPoolExecutor` job in that of its submitter, and an item taken from a `queue.Queue`
makes the consumer act for the producer's task, as external task `queue_consumer`.
"""

from __future__ import annotations

import contextvars
import functools
import http.client
import inspect
import io
import json
import os
import queue
import re
import sys
import threading
import uuid
from collections import deque
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field
from typing import Any
from urllib.parse import urlsplit

import lgtrace

MEM_PREFIX = "mem:"
DB_PREFIX = "db:"
HTTP_PREFIX = "http:"
SCAN_BUDGET = 200_000
ROOT_BUDGET = 5_000
DB_ROWS = 200


# ---------------------------------------------------------------------------------------------
# 2 process memory


def _marker_lines(texts: Iterable[str], markers: Iterable[str]) -> set[str]:
  ms = tuple(markers)
  return {ln for t in texts for ln in t.splitlines() if any(m in ln for m in ms)}


def _strings(root: Any, budget: list[int], markers: tuple[str, ...]) -> list[str]:
  """Strings carrying a marker below `root`, through containers, attributes and slots, while
  `budget` lasts. Modules, functions and classes are not entered."""
  out: list[str] = []
  stack, seen = [root], set()
  while stack and budget[0] > 0:
    x = stack.pop()
    budget[0] -= 1
    if isinstance(x, str):
      if any(m in x for m in markers):
        out.append(x)
      continue
    if isinstance(x, bytes | bytearray):
      if len(x) < 1 << 20:
        s = bytes(x).decode(errors="replace")
        if any(m in s for m in markers):
          out.append(s)
      continue
    if x is None or isinstance(x, int | float | bool | complex) or id(x) in seen:
      continue
    if inspect.ismodule(x) or inspect.isroutine(x) or isinstance(x, type):
      continue
    seen.add(id(x))
    try:
      if isinstance(x, Mapping):
        stack.extend(v for kv in list(x.items())[:2000] for v in kv)
      elif isinstance(x, list | tuple | set | frozenset | deque):
        stack.extend(list(x)[:2000])
      d = getattr(x, "__dict__", None)
      if isinstance(d, dict):
        stack.extend(d.values())
      for cls in type(x).__mro__:
        for s in getattr(cls, "__slots__", ()) or ():
          if isinstance(s, str) and hasattr(x, s):
            stack.append(getattr(x, s))
    except Exception:  # noqa: BLE001, an object that refuses inspection is skipped
      continue
  return out


@dataclass
class MemoryWatch:
  """Marker-carrying lines of app globals, rescanned at task boundaries (module docstring)."""
  root: str
  markers: tuple[str, ...] = ()
  lines: dict[str, frozenset[str]] = field(default_factory=dict)
  lock: Any = field(default_factory=threading.RLock)
  enabled: bool = True

  def roots(self) -> Iterable[tuple[str, Any]]:
    for name, mod in list(sys.modules.items()):
      f = getattr(mod, "__file__", None) or ""
      if not f.startswith(self.root) or name.startswith("lgauto"):
        continue
      for k, v in list(vars(mod).items()):
        if k.startswith("__") or inspect.ismodule(v) or inspect.isroutine(v):
          if inspect.isroutine(v) and getattr(v, "__module__", None) == name:
            yield from self._closure(f"{name}.{k}", v)
          continue
        if isinstance(v, type):
          if v.__module__ == name:
            yield from ((f"{name}.{k}.{ck}", cv) for ck, cv in list(vars(v).items())
                        if not ck.startswith("__") and not inspect.isroutine(cv)
                        and not isinstance(cv, property | staticmethod | classmethod))
          continue
        yield f"{name}.{k}", v

  @staticmethod
  def _closure(path: str, fn: Any) -> Iterable[tuple[str, Any]]:
    """Cells of a module-level function's closure, such as a decorator's cache dict."""
    fn = inspect.unwrap(fn) if hasattr(fn, "__wrapped__") else fn
    for i, cell in enumerate(getattr(fn, "__closure__", None) or ()):
      try:
        v = cell.cell_contents
      except ValueError:
        continue
      if isinstance(v, dict | list | set | deque) or hasattr(v, "__dict__") \
          and not inspect.isroutine(v) and not isinstance(v, type):
        yield f"{path}.<closure{i}>", v

  def scan(self) -> dict[str, frozenset[str]]:
    """Each global gets `ROOT_BUDGET` objects of the walk, so one large global (a config, a
    compiled graph) cannot starve the others, and all of them `SCAN_BUDGET`."""
    total = SCAN_BUDGET
    found: dict[str, frozenset[str]] = {}
    for path, value in self.roots():
      if total <= 0:
        break
      budget = [min(ROOT_BUDGET, total)]
      ls = _marker_lines(_strings(value, budget, self.markers), self.markers)
      total -= min(ROOT_BUDGET, total) - budget[0]
      if ls:
        found[path] = frozenset(ls)
    return found

  def _write(self, now: dict[str, frozenset[str]]) -> None:
    for path, ls in now.items():
      if ls - self.lines.get(path, frozenset()):
        lgtrace.emit(MEM_PREFIX + path, "write", sorted(ls))
    self.lines = now

  def _read(self, now: Mapping[str, frozenset[str]], produced: Any) -> None:
    texts = [t for t in lgtrace.leaves(produced) if any(m in t for m in self.markers)]
    for path, ls in now.items() if texts else ():
      hit = sorted(ln for ln in ls if any(ln in t for t in texts))
      if hit:
        lgtrace.emit(MEM_PREFIX + path, "read", hit)

  def write(self) -> None:
    """Record, for the current task, every global that gained marker-carrying lines."""
    if self.enabled and self.markers:
      with self.lock:
        self._write(self.scan())

  def task_end(self, produced: Any) -> None:
    """At the end of a task's code, or of an LLM call or tool input, its reads of globals whose
    lines occur in what it produced, then its writes."""
    if self.enabled and self.markers:
      with self.lock:
        now = self.scan()
        self._read(now, produced)
        self._write(now)


MEMORY = MemoryWatch("")


def install_memory(root: str, markers: Iterable[str]) -> MemoryWatch:
  """Watch app globals, and rescan them at the end of every tracked node and routing function."""
  MEMORY.root = os.path.realpath(root)
  MEMORY.markers = tuple(markers)
  cls = lgtrace._tracked_runnable_class()
  if getattr(cls, "_lgseams", False):
    return MEMORY
  invoke, ainvoke = cls.invoke, cls.ainvoke

  def tracked_invoke(self: Any, input: Any, config: Any = None, **kwargs: Any) -> Any:
    out = invoke(self, input, config, **kwargs)
    MEMORY.task_end(out)
    return out

  async def tracked_ainvoke(self: Any, input: Any, config: Any = None, **kwargs: Any) -> Any:
    out = await ainvoke(self, input, config, **kwargs)
    MEMORY.task_end(out)
    return out
  cls.invoke, cls.ainvoke = tracked_invoke, tracked_ainvoke
  cls._lgseams = True
  return MEMORY


# ---------------------------------------------------------------------------------------------
# 4 embedded databases


_TABLE = re.compile(
  r"\b(?:from|join|into|update|table|view|exists|describe)\s+((?:\"[^\"]+\"|[\w$]+)"
  r"(?:\.(?:\"[^\"]+\"|[\w$]+))*)", re.I)
_WRITES = re.compile(r"^\s*(insert|update|delete|create|replace|copy|alter|drop|merge|upsert)\b",
                     re.I)
_KEYWORDS = frozenset({"select", "not", "if", "exists", "where", "values", "set", "as", "on",
                       "the", "read_csv", "read_csv_auto", "read_parquet", "read_json"})
_DB_COUNT = iter(range(10**9))


def sql_tables(sql: str) -> list[str]:
  """Table names a statement names after FROM, JOIN, INTO, UPDATE, TABLE or VIEW."""
  names = [n.replace('"', "") for n in _TABLE.findall(sql or "")]
  return list(dict.fromkeys(n for n in names if n.lower() not in _KEYWORDS
                            and not n.lower().startswith(("read_", "(")))) or ["?"]


def _db_name(engine: str, database: Any) -> str:
  db = os.fsdecode(database) if isinstance(database, str | bytes | os.PathLike) else ""
  if db and db not in (":memory:", "") and not db.startswith(":memory:"):
    return f"{engine}:{os.path.basename(db)}"
  return f"{engine}{next(_DB_COUNT)}"


def _record_statement(name: str, sql: str, snapshot: Callable[[str], Any], write: bool,
                      run: Callable[[], Any]) -> Any:
  """Run a statement and record it per table: rows read first, rows written after."""
  tables = sql_tables(sql)
  if not write:
    try:
      rows = snapshot(sql)
    except Exception:  # noqa: BLE001, a statement the snapshot cannot repeat
      rows = None
    out = run()
    for t in tables:
      lgtrace.emit(f"{DB_PREFIX}{name}/{t}", "read", rows)
    return out
  out = run()
  for t in tables:
    try:
      rows = snapshot(f"SELECT * FROM {t} LIMIT {DB_ROWS}")
    except Exception:  # noqa: BLE001, a dropped table or a schema statement
      rows = None
    lgtrace.emit(f"{DB_PREFIX}{name}/{t}", "write", rows)
  return out


def _sqlite_classes() -> tuple[type, type]:
  import sqlite3

  class RecCursor(sqlite3.Cursor):
    def execute(self, sql: str, params: Any = (), /) -> Any:
      conn = self.connection
      return _record_statement(conn._lgseams_name, sql, conn._lgseams_rows,
                               bool(_WRITES.match(sql)),
                               lambda: sqlite3.Cursor.execute(self, sql, params))

    def executemany(self, sql: str, seq: Any, /) -> Any:
      seq = list(seq)
      conn = self.connection
      return _record_statement(conn._lgseams_name, sql, conn._lgseams_rows, True,
                               lambda: sqlite3.Cursor.executemany(self, sql, seq))

  class RecConnection(sqlite3.Connection):
    def __init__(self, database: Any, *args: Any, **kwargs: Any) -> None:
      super().__init__(database, *args, **kwargs)
      self._lgseams_name = _db_name("sqlite", database)

    def _lgseams_rows(self, sql: str) -> Any:
      return sqlite3.Connection.execute(self, sql).fetchmany(DB_ROWS)

    def cursor(self, factory: Any = None) -> Any:
      return super().cursor(factory or RecCursor)

    def execute(self, sql: str, params: Any = (), /) -> Any:
      return self.cursor().execute(sql, params)

    def executemany(self, sql: str, seq: Any, /) -> Any:
      return self.cursor().executemany(sql, seq)
  return RecConnection, RecCursor


class DuckProxy:
  """A DuckDB connection that records its statements, delegating everything else."""

  def __init__(self, conn: Any, name: str) -> None:
    object.__setattr__(self, "_conn", conn)
    object.__setattr__(self, "_name", name)

  def __getattr__(self, attr: str) -> Any:
    return getattr(self._conn, attr)

  def __setattr__(self, attr: str, value: Any) -> None:
    setattr(self._conn, attr, value)

  def __enter__(self) -> DuckProxy:
    return self

  def __exit__(self, *exc: Any) -> None:
    self._conn.close()

  def _rows(self, sql: str) -> Any:
    return self._conn.cursor().execute(sql).fetchmany(DB_ROWS)

  def _run(self, method: str, sql: str, *args: Any, **kwargs: Any) -> Any:
    out = _record_statement(self._name, sql, self._rows, bool(_WRITES.match(sql)),
                            lambda: getattr(self._conn, method)(sql, *args, **kwargs))
    return self if out is self._conn else out

  def execute(self, sql: str, *args: Any, **kwargs: Any) -> Any:
    return self._run("execute", sql, *args, **kwargs)

  def sql(self, sql: str, *args: Any, **kwargs: Any) -> Any:
    return self._run("sql", sql, *args, **kwargs)

  def query(self, sql: str, *args: Any, **kwargs: Any) -> Any:
    return self._run("query", sql, *args, **kwargs)

  def executemany(self, sql: str, *args: Any, **kwargs: Any) -> Any:
    return self._run("executemany", sql, *args, **kwargs)

  def register(self, view: str, obj: Any) -> Any:
    out = self._conn.register(view, obj)
    try:
      rows = self._rows(f"SELECT * FROM {view} LIMIT {DB_ROWS}")
    except Exception:  # noqa: BLE001
      rows = None
    lgtrace.emit(f"{DB_PREFIX}{self._name}/{view}", "write", rows)
    return self if out is self._conn else out

  def cursor(self) -> DuckProxy:
    return DuckProxy(self._conn.cursor(), self._name)


def install_db() -> None:
  """Record sqlite3 and duckdb statements per database and table."""
  import sqlite3
  if not getattr(sqlite3, "_lgseams", False):
    rec_conn, _ = _sqlite_classes()
    connect = sqlite3.connect

    @functools.wraps(connect)
    def rec_connect(database: Any, *args: Any, **kwargs: Any) -> Any:
      if "factory" not in kwargs and len(args) < 4:
        kwargs["factory"] = rec_conn
      return connect(database, *args, **kwargs)
    sqlite3.connect = rec_connect
    sqlite3._lgseams = True  # type: ignore[attr-defined]
  try:
    import duckdb
  except ImportError:
    return
  if getattr(duckdb, "_lgseams", False):
    return
  dconnect = duckdb.connect

  @functools.wraps(dconnect)
  def duck_connect(database: Any = ":memory:", *args: Any, **kwargs: Any) -> Any:
    db = kwargs.get("database", database)
    return DuckProxy(dconnect(database, *args, **kwargs), _db_name("duckdb", db))
  duckdb.connect = duck_connect
  default: list[DuckProxy] = []

  def module_level(method: str) -> Callable[..., Any]:
    def call(sql: str, *args: Any, **kwargs: Any) -> Any:
      if not default:
        default.append(DuckProxy(duckdb.default_connection() if callable(getattr(
          duckdb, "default_connection", None)) else dconnect(), "duckdb-default"))
      return getattr(default[0], method)(sql, *args, **kwargs)
    return call
  for method in ("sql", "query", "execute"):
    if hasattr(duckdb, method):
      setattr(duckdb, method, module_level(method))
  duckdb._lgseams = True  # type: ignore[attr-defined]


# ---------------------------------------------------------------------------------------------
# 5 network services


def _parse_body(body: bytes, ctype: str = "") -> Any:
  text = body.decode(errors="replace")
  if "json" in ctype or text[:1] in "{[":
    try:
      return json.loads(text)
    except ValueError:
      pass
  return text


@dataclass
class FakeService:
  """Every remote host at once, as a key-value store over host and path (module docstring)."""
  objects: dict[str, tuple[str, bytes]] = field(default_factory=dict)
  lock: Any = field(default_factory=threading.Lock)
  requests: list[str] = field(default_factory=list)

  def handle(self, method: str, url: str, headers: Mapping[str, str],
             body: bytes) -> tuple[int, dict[str, str], bytes]:
    parts = urlsplit(url)
    channel = f"{HTTP_PREFIX}{parts.hostname or '?'}{parts.path or '/'}"
    method = method.upper()
    ctype = next((v for k, v in headers.items() if k.lower() == "content-type"), "")
    with self.lock:
      self.requests.append(f"{method} {channel}")
    if b'"jsonrpc"' in body[:200] or "text/event-stream" in str(headers).lower():
      # A session protocol (MCP, JSON-RPC, SSE) waits for replies a store cannot give, so the
      # service refuses it, as an unreachable server would.
      lgtrace.emit(channel, "write", _parse_body(body, ctype))
      return 503, {"Content-Type": "text/plain"}, b"lgauto: protocol service not modelled"
    if method in ("PUT", "POST", "PATCH"):
      lgtrace.emit(channel, "write", _parse_body(body, ctype))
      with self.lock:
        self.objects[channel] = (ctype or "application/octet-stream", body)
      seen = " ".join(m for m in _markers() if m in body.decode(errors="replace"))
      reply = json.dumps({"id": uuid.uuid4().hex, "status": "ok", "content": f"[http] {seen}"})
      return 200, {"Content-Type": "application/json", "ETag": '"lgauto"'}, reply.encode()
    if method == "DELETE":
      lgtrace.emit(channel, "write", None)
      with self.lock:
        self.objects.pop(channel, None)
      return 204, {}, b""
    with self.lock:
      stored = self.objects.get(channel)
    if stored is not None:
      lgtrace.emit(channel, "read", _parse_body(stored[1], stored[0]))
      return 200, {"Content-Type": stored[0], "ETag": '"lgauto"'}, stored[1]
    seen = " ".join(m for m in _markers() if m in url)
    reply = json.dumps({"status": "ok", "content": f"[http] {seen}".strip()}).encode()
    lgtrace.emit(channel, "read", None)
    return 200, {"Content-Type": "application/json"}, reply


SERVICE = FakeService()
_MARKERS: list[str] = []


def _markers() -> list[str]:
  return _MARKERS


def _reply_bytes(status: int, headers: Mapping[str, str], body: bytes, head: bool) -> bytes:
  lines = [f"HTTP/1.1 {status} {http.client.responses.get(status, 'OK')}",
           *(f"{k}: {v}" for k, v in headers.items()), f"Content-Length: {len(body)}",
           "Connection: close", "", ""]
  return "\r\n".join(lines).encode() + (b"" if head else body)


def _split_request(raw: bytes) -> tuple[str, str, dict[str, str], bytes]:
  head, _, body = raw.partition(b"\r\n\r\n")
  lines = head.decode(errors="replace").split("\r\n")
  method, target = (lines[0].split(" ") + ["", ""])[:2]
  headers = dict(ln.split(": ", 1) for ln in lines[1:] if ": " in ln)
  if any(k.lower() == "transfer-encoding" and "chunked" in v for k, v in headers.items()):
    out, rest = bytearray(), body
    while rest:
      size, _, rest = rest.partition(b"\r\n")
      n = int(size.split(b";")[0] or b"0", 16)
      if n == 0:
        break
      out += rest[:n]
      rest = rest[n + 2:]
    body = bytes(out)
  return method, target, headers, body


class FakeSocket:
  """What `http.client` writes to and reads from in place of a socket."""

  def __init__(self, conn: Any) -> None:
    self.conn = conn
    self.sent = bytearray()

  def sendall(self, data: Any) -> None:
    self.sent += bytes(data)

  def send(self, data: Any) -> int:
    self.sent += bytes(data)
    return len(data)

  def makefile(self, *args: Any, **kwargs: Any) -> io.BytesIO:
    method, target, headers, body = _split_request(bytes(self.sent))
    self.sent.clear()
    host = headers.get("Host") or getattr(self.conn, "host", "?")
    scheme = "https" if isinstance(self.conn, http.client.HTTPSConnection) else "http"
    url = target if "://" in target else f"{scheme}://{host}{target}"
    status, rh, rbody = SERVICE.handle(method, url, headers, body)
    return io.BytesIO(_reply_bytes(status, rh, rbody, method.upper() == "HEAD"))

  def settimeout(self, *a: Any) -> None:
    pass

  def setsockopt(self, *a: Any) -> None:
    pass

  def gettimeout(self) -> None:
    return None

  def close(self) -> None:
    pass

  def shutdown(self, *a: Any) -> None:
    pass

  def fileno(self) -> int:
    return -1


def _fake_connect(self: Any) -> None:
  self.sock = FakeSocket(self)


def install_http(markers: Iterable[str]) -> None:
  """No HTTP request leaves the process. `FakeService` answers each one and records it."""
  _MARKERS[:] = list(markers)
  if getattr(http.client, "_lgseams", False):
    return
  http.client.HTTPConnection.connect = _fake_connect  # type: ignore[method-assign]
  http.client.HTTPSConnection.connect = _fake_connect  # type: ignore[method-assign]
  http.client._lgseams = True  # type: ignore[attr-defined]
  try:
    import urllib3.connection
    import urllib3.util.connection as uconn
    for cls in (urllib3.connection.HTTPConnection, urllib3.connection.HTTPSConnection):
      cls.connect = _fake_connect
    uconn.is_connection_dropped = lambda conn: False
    import urllib3.connectionpool as pool
    if hasattr(pool, "is_connection_dropped"):
      pool.is_connection_dropped = lambda conn: False
  except ImportError:
    pass
  try:
    import httpx

    def handle(self: Any, request: Any) -> Any:
      body = request.read()
      status, headers, content = SERVICE.handle(request.method, str(request.url),
                                                dict(request.headers), body)
      return httpx.Response(status, headers=headers, content=content, request=request)

    async def ahandle(self: Any, request: Any) -> Any:
      body = await request.aread()
      status, headers, content = SERVICE.handle(request.method, str(request.url),
                                                dict(request.headers), body)
      return httpx.Response(status, headers=headers, content=content, request=request)
    httpx.HTTPTransport.handle_request = handle
    httpx.AsyncHTTPTransport.handle_async_request = ahandle
  except ImportError:
    pass
  try:
    import aiohttp
    request = aiohttp.ClientSession._request

    async def refused(self: Any, method: str, url: Any, *args: Any, **kwargs: Any) -> Any:
      body = kwargs.get("data") or kwargs.get("json")
      channel = f"{HTTP_PREFIX}{urlsplit(str(url)).hostname}{urlsplit(str(url)).path}"
      lgtrace.emit(channel, "write" if method.upper() in ("PUT", "POST", "PATCH") else "read",
                   body)
      raise aiohttp.ClientConnectionError(f"lgauto: network disabled ({url})")
    aiohttp.ClientSession._request = refused
    del request
  except ImportError:
    pass


# ---------------------------------------------------------------------------------------------
# 7 carriers


def install_carriers() -> None:
  """Threads and pool jobs run in their starter's context, and a `queue.Queue` item makes its
  consumer act for the producer's task."""
  import concurrent.futures
  if getattr(threading, "_lgseams", False):
    return
  start = threading.Thread.start

  def ctx_start(self: threading.Thread) -> None:
    ctx = contextvars.copy_context()
    target = self.run

    def run() -> None:
      ctx.run(target)
      ctx.run(MEMORY.write)
    self.run = run  # type: ignore[method-assign]
    start(self)
  threading.Thread.start = ctx_start  # type: ignore[method-assign]
  submit = concurrent.futures.ThreadPoolExecutor.submit

  def ctx_submit(self: Any, fn: Callable[..., Any], /, *args: Any, **kwargs: Any) -> Any:
    return submit(self, contextvars.copy_context().run, fn, *args, **kwargs)
  concurrent.futures.ThreadPoolExecutor.submit = ctx_submit  # type: ignore[method-assign]

  put, get = queue.Queue._put, queue.Queue._get

  def q_put(self: Any, item: Any) -> None:
    put(self, item)
    if type(self) is queue.Queue:
      self.__dict__.setdefault("_lgseams_tasks", deque()).append(lgtrace.current_task())

  def q_get(self: Any) -> Any:
    item = get(self)
    tasks = self.__dict__.get("_lgseams_tasks")
    if type(self) is queue.Queue and tasks:
      producer = tasks.popleft()
      if producer is not None and producer != lgtrace.current_task():
        tid = f"ext-{uuid.uuid4().hex[:12]}"
        lgtrace.RESOURCES.add_task(lgtrace.ExternalTask(tid, "queue_consumer", None, producer,
                                                        lgtrace.tick()))
        lgtrace._ACTOR.set(tid)
    return item
  queue.Queue._put, queue.Queue._get = q_put, q_get  # type: ignore[method-assign]
  threading._lgseams = True  # type: ignore[attr-defined]
