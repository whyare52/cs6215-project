"""Zero-config checking with `lgauto`, on small apps written to a temp dir.

The pure parts (schema filling, decision trees, config parsing, SQL tables, the fake service)
run anywhere. The end-to-end tests need LangGraph and langchain-core in this interpreter and
run `python -m lgauto` as the CLI does.
"""

import importlib.util
import json
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

PY_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PY_DIR))

import lgauto  # noqa: E402
import lgseams  # noqa: E402

HAS_LANGGRAPH = all(importlib.util.find_spec(m) for m in ("langgraph", "langchain_core", "httpx"))

ROUTER_APP = '''
from typing import Literal

from langchain_core.language_models.fake_chat_models import FakeListChatModel
from langgraph.graph import END, START, MessagesState, StateGraph
from langgraph.store.base import BaseStore
from pydantic import BaseModel

llm = FakeListChatModel(responses=["hi"])


class Route(BaseModel):
  action: Literal["answer", "remember"]
  note: str


def route(state: MessagesState, *, store: BaseStore):
  r = llm.with_structured_output(Route).invoke(state["messages"])
  if r.action == "remember":
    store.put(("notes",), "last", {"note": r.note})
  return {}


def answer(state: MessagesState, *, store: BaseStore):
  ctx = " ".join(i.value["note"] for i in store.search(("notes",)))
  return {"messages": [llm.invoke([("system", ctx), *state["messages"]])]}


builder = StateGraph(MessagesState)
builder.add_node("route", route)
builder.add_node("answer", answer)
builder.add_edge(START, "route")
builder.add_edge("route", "answer")
builder.add_edge("answer", END)
graph = builder.compile()
'''

CATALOGUE_APP = '''
import sqlite3
import threading

import httpx
from langchain_core.language_models.fake_chat_models import FakeListChatModel
from langgraph.graph import END, START, MessagesState, StateGraph

llm = FakeListChatModel(responses=["hi"])
_CACHE = {}
DB = sqlite3.connect(":memory:", check_same_thread=False)
DB.execute("CREATE TABLE notes (body TEXT)")
SEAM = "__SEAM__"


def remember(state: MessagesState):
  text = state["messages"][-1].content
  if SEAM == "mem":
    threading.Timer(0.05, lambda: _CACHE.__setitem__("last", text)).start()
  if SEAM == "db":
    DB.execute("INSERT INTO notes VALUES (?)", (text,))
  if SEAM == "http":
    httpx.put("http://bucket.example/notes/last", content=text.encode())
  return {}


def make_graph(config):
  prompt = _CACHE.get("last", "")
  if SEAM == "db":
    prompt = " ".join(r[0] for r in DB.execute("SELECT body FROM notes").fetchall())
  if SEAM == "http":
    prompt = httpx.get("http://bucket.example/notes/last").text

  def chat(state: MessagesState):
    return {"messages": [llm.invoke([("system", prompt), *state["messages"]])]}
  b = StateGraph(MessagesState)
  b.add_node("chat", chat)
  b.add_node("remember", remember)
  b.add_edge(START, "chat")
  b.add_edge("chat", "remember")
  b.add_edge("remember", END)
  return b.compile()
'''


SERVICE_STARTUP = '''
import asyncio
import os

CONN = {}


async def startup():
  """The app's startup: a connection to its service, bound to the loop it was opened on."""
  CONN["rw"] = await asyncio.open_connection("127.0.0.1", int(os.environ["ECHO_PORT"]))
'''

SERVICE_APP = '''
from langgraph.graph import END, START, MessagesState, StateGraph

from app.server import CONN


async def chat(state: MessagesState):
  reader, writer = CONN["rw"]
  writer.write(state["messages"][-1].content.encode() + b"\\n")
  await writer.drain()
  line = await reader.readline()
  return {"messages": [("ai", "echo " + line.decode().strip())]}


b = StateGraph(MessagesState)
b.add_node("chat", chat)
b.add_edge(START, "chat")
b.add_edge("chat", END)
graph = b.compile()
'''


def echo_server():
  """A line echo service on a free local port, served from a thread."""
  import socketserver
  import threading

  class Echo(socketserver.StreamRequestHandler):
    def handle(self):
      for line in self.rfile:
        self.wfile.write(line)
  server = socketserver.ThreadingTCPServer(("127.0.0.1", 0), Echo)
  server.daemon_threads = True
  threading.Thread(target=server.serve_forever, daemon=True).start()
  return server


def write_app(root: Path, source: str, graph: str = "./app/graph.py:graph") -> Path:
  (root / "app").mkdir(parents=True)
  (root / "app" / "graph.py").write_text(textwrap.dedent(source))
  (root / "langgraph.json").write_text(json.dumps({"graphs": {"agent": graph}}))
  return root


def run_cli(repo: Path, *args: str) -> dict:
  proc = subprocess.run([sys.executable, "-m", "lgauto", str(repo), "--no-write", *args],
                        cwd=PY_DIR, capture_output=True, text=True, timeout=600)
  if proc.returncode:
    raise AssertionError(f"lgauto failed:\n{proc.stdout[-2000:]}\n{proc.stderr[-3000:]}")
  line = next(ln for ln in proc.stdout.splitlines() if ln.startswith("LGAUTO_JSON "))
  return json.loads(line.removeprefix("LGAUTO_JSON "))[0]


class SchemaTests(unittest.TestCase):
  def setUp(self):
    lgauto.CURRENT.used.clear()
    lgauto.CURRENT.choices.clear()
    lgauto.CURRENT.principal = "A"

  def test_enum_and_bool_fields_are_decisions(self):
    schema = {"type": "object", "properties": {
      "route": {"enum": ["ignore", "respond"]}, "ask": {"type": "boolean"},
      "why": {"type": "string"}}}
    lgauto.CURRENT.choices["A|p.route"] = 1
    v = lgauto.fill_schema(schema, "p", "MKx")
    self.assertEqual(v["route"], "respond")
    self.assertIs(v["ask"], False)
    self.assertIn("MKx", v["why"])
    self.assertEqual(set(lgauto.CURRENT.used), {"A|p.route", "A|p.ask"})

  def test_refs_and_optional_fields(self):
    schema = {"$defs": {"Item": {"type": "object", "properties": {"t": {"type": "string"}}}},
              "type": "object", "properties": {
                "items": {"type": "array", "items": {"$ref": "#/$defs/Item"}},
                "maybe": {"anyOf": [{"type": "null"}, {"type": "integer"}]}}}
    v = lgauto.fill_schema(schema, "p", "MKx")
    self.assertIn("MKx", v["items"][0]["t"])
    self.assertIsInstance(v["maybe"], int)

  def test_json_template_reads_a_prompt_format_leniently(self):
    prompt = 'Return {{ "facts": [{{ "content": "...", "confidence": 0.0-1.0 }}], ' \
             '"ok": true/false }}'
    t = lgauto.json_template(prompt)
    self.assertEqual(t, {"facts": [{"content": "...", "confidence": 1.0}], "ok": True})
    filled = lgauto.fill_template(t, "MKx")
    self.assertIn("MKx", filled["facts"][0]["content"])
    self.assertIsNone(lgauto.json_template("no format here"))

  def test_input_fills_messages_required_text_and_ids(self):
    schema = {"type": "object", "required": ["query", "user_id"], "properties": {
      "messages": {"type": "array"}, "query": {"type": "string"},
      "user_id": {"type": "string"}, "notes": {"type": "string"}}}
    inp = lgauto.fill_input(schema, "B", "MKb")
    self.assertEqual(set(inp), {"messages", "query", "user_id"})
    self.assertIn("MKb", inp["messages"][0]["content"])
    self.assertIn("MKb", inp["query"])
    self.assertEqual(inp["user_id"], "user-B")


class ExploreTests(unittest.TestCase):
  def test_tree_covers_every_reachable_combination_once(self):
    """`x` has two options and only its second option reaches decision `y`, with three."""
    def run(choices):
      used = {"x": ["0", "1"]}
      if choices.get("x", 0) == 1:
        used["y"] = ["0", "1", "2"]
      return (choices.get("x", 0), choices.get("y", 0)), used
    kept = lgauto.explore(run, 50)
    self.assertEqual(sorted(r for _, r, _ in kept), [(0, 0), (1, 0), (1, 1), (1, 2)])

  def test_budget(self):
    kept = lgauto.explore(lambda c: (None, {f"k{i}": ["a", "b"] for i in range(6)}), 5)
    self.assertEqual(len(kept), 5)


class ConfigTests(unittest.TestCase):
  def test_langgraph_json_paths_and_modules(self):
    with tempfile.TemporaryDirectory() as d:
      root = Path(d)
      (root / "backend").mkdir()
      (root / "backend" / "langgraph.json").write_text(json.dumps({
        "graphs": {"a": "./src/g.py:graph", "b": "pkg.mod:make"},
        "dependencies": [".", "./src", "langchain_openai"], "env": ".env",
        "store": {"index": {"dims": 8}}}))
      cfg = lgauto.app_config(root)
      self.assertEqual(cfg.base, "backend")
      self.assertEqual([(g.file, g.module, g.attr) for g in cfg.graphs],
                       [("src/g.py", "", "graph"), ("", "pkg.mod", "make")])
      self.assertEqual(cfg.dependencies, ("backend", "backend/src"))
      self.assertEqual(cfg.store_index, {"dims": 8})

  def test_scan_without_config(self):
    with tempfile.TemporaryDirectory() as d:
      root = write_app(Path(d), ROUTER_APP)
      (root / "langgraph.json").unlink()
      names = [g.attr for g in lgauto.app_config(root).graphs]
      self.assertIn("graph", names)
      self.assertIn("builder", names)

  def test_env_file_falls_back_to_example(self):
    with tempfile.TemporaryDirectory() as d:
      root = Path(d)
      (root / ".env.example").write_text("# c\nexport A=1\nB='two words'\nC=\n")
      cfg = lgauto.AppConfig("langgraph.json", ".", (), ".env")
      self.assertEqual(lgauto.config_env(root, cfg), {"A": "1", "B": "two words", "C": ""})

  def test_env_file_found_by_convention_without_config(self):
    with tempfile.TemporaryDirectory() as d:
      root = Path(d)
      (root / ".env.dev").write_text("MINIO_ENDPOINT=localhost:9000\n")
      cfg = lgauto.AppConfig("", ".", (), {})
      self.assertEqual(lgauto.config_env(root, cfg), {"MINIO_ENDPOINT": "localhost:9000"})

  def test_factory_runtime_parameter_gets_the_user(self):
    import inspect

    def graph(runtime):
      return runtime
    param = inspect.signature(graph).parameters["runtime"]
    config = {"configurable": {"langgraph_auth_user": "alice"}}
    rt = lgauto.factory_arg(param, config)
    self.assertEqual(rt.user, "alice")
    self.assertFalse(rt.context)

  def test_namespace_package_module_imports_from_the_app_root(self):
    with tempfile.TemporaryDirectory() as d:
      root = Path(d)
      (root / "nsapp").mkdir()
      (root / "nsapp" / "state.py").write_text("X = 1\n")
      (root / "nsapp" / "graph.py").write_text("from .state import X\nY = X + 1\n")
      cfg = lgauto.AppConfig("", ".", (), {})
      ref = lgauto.GraphRef("g", "Y", "nsapp/graph.py", "")
      try:
        self.assertEqual(lgauto.load_attr(root, cfg, ref), 2)
      finally:
        for m in ("nsapp", "nsapp.graph", "nsapp.state", "graph", "state"):
          sys.modules.pop(m, None)


class ServiceAndStartupTests(unittest.TestCase):
  def test_service_addresses_expand_local_names(self):
    got = lgauto.service_addresses(["localhost:5432", "db.internal:6379"])
    self.assertEqual(got, {("localhost", 5432), ("127.0.0.1", 5432), ("::1", 5432),
                           ("db.internal", 6379)})
    with self.assertRaises(ValueError):
      lgauto.service_addresses(["5432"])

  def test_ids_read_as_keys_and_attributes(self):
    ids = lgauto.Ids(thread_id="t", user_id="u")
    self.assertEqual((ids["thread_id"], ids.thread_id, getattr(ids, "model", None)),
                     ("t", "t", None))

  def test_factory_class_context_schema_fills_an_undeclared_context(self):
    import dataclasses

    @dataclasses.dataclass
    class Ctx:
      thread_id: str = ""
      user_id: str = ""
      model: str = "openai/gpt-4"

    class Agent:
      context_schema = Ctx

      def get_graph(self, context=None):
        return None

    def plain():
      return None
    self.assertIs(lgauto.factory_context_schema(Agent().get_graph), Ctx)
    self.assertIsNone(lgauto.factory_context_schema(plain))
    graph = type("G", (), {"context_schema": None})()
    ctx = lgauto.context_for(graph, "A", "thread-A", Ctx)
    self.assertEqual((ctx.thread_id, ctx.user_id, ctx.model),
                     ("thread-A", lgauto.user_id("A"), "openai/gpt-4"))
    self.assertIsInstance(lgauto.context_for(graph, "A", "thread-A"), lgauto.Ids)

  def test_start_app_enters_each_kind_of_startup_and_keeps_it_open(self):
    import contextlib
    events = []

    @contextlib.asynccontextmanager
    async def lifespan(app):
      events.append(("lifespan", app))
      yield
      events.append("closed")

    class App:  # a Starlette app's shape
      class router:
        @staticmethod
        def lifespan_context(app):
          return lifespan(app)

    async def coro():
      events.append("async")
    loop = lgauto.AppLoop()
    for target in (lifespan, App, coro, lambda: events.append("sync")):
      loop.run(lgauto.start_app(target, loop.stack))
    self.assertEqual(events, [("lifespan", None), ("lifespan", App), "async", "sync"])


class SeamUnitTests(unittest.TestCase):
  def test_sql_tables(self):
    self.assertEqual(lgseams.sql_tables("SELECT * FROM payroll.payroll p JOIN x ON 1"),
                     ["payroll.payroll", "x"])
    self.assertEqual(lgseams.sql_tables("CREATE TABLE IF NOT EXISTS t AS SELECT 1"), ["t"])
    self.assertEqual(lgseams.sql_tables("SELECT 1"), ["?"])

  def test_fake_service_stores_and_returns(self):
    svc = lgseams.FakeService()
    svc.handle("PUT", "http://h/b/k", {"Content-Type": "text/plain"}, b"body")
    status, _, body = svc.handle("GET", "http://h/b/k", {}, b"")
    self.assertEqual((status, body), (200, b"body"))
    self.assertEqual(svc.handle("GET", "http://h/other", {}, b"")[0], 200)

  def test_fake_service_refuses_session_protocols(self):
    """An MCP client over JSON-RPC would wait forever on a stored-object reply."""
    svc = lgseams.FakeService()
    body = b'{"jsonrpc": "2.0", "method": "initialize", "id": 0}'
    self.assertEqual(svc.handle("POST", "http://h/mcp", {}, body)[0], 503)

  def test_split_chunked_request(self):
    raw = (b"POST /x HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\n\r\n"
           b"4\r\nwiki\r\n5\r\npedia\r\n0\r\n\r\n")
    self.assertEqual(lgseams._split_request(raw), ("POST", "/x", {
      "Host": "h", "Transfer-Encoding": "chunked"}, b"wikipedia"))


@unittest.skipUnless(HAS_LANGGRAPH, "needs langgraph, langchain-core and httpx")
class EndToEndTests(unittest.TestCase):
  def test_router_branch_found_by_enumerating_literal(self):
    with tempfile.TemporaryDirectory() as d:
      s = run_cli(write_app(Path(d), ROUTER_APP))
    self.assertTrue(s["ran"])
    self.assertEqual(s["setup"], [])
    self.assertIn("answer@B", s["findings"])
    self.assertTrue(any("store:notes#A" in step for step in s["findings"]["answer@B"]))
    self.assertGreater(s["scripts"], 1)
    self.assertEqual(s["unexplained"], [])
    self.assertEqual(s["nodes_ran"], ["answer", "route"])

  def test_each_catalogue_seam_carries_the_leak(self):
    for seam, channel in (("mem", "mem:graph._CACHE"), ("db", "db:sqlite0/notes"),
                          ("http", "http:bucket.example/notes/last")):
      with self.subTest(seam=seam), tempfile.TemporaryDirectory() as d:
        app = write_app(Path(d), CATALOGUE_APP.replace("__SEAM__", seam), "./app/graph.py:make_graph")
        s = run_cli(app)
        self.assertIn("chat@B", s["findings"], s)
        steps = " ".join(s["findings"]["chat@B"])
        self.assertIn(f"{channel}#A", steps)
        self.assertEqual(s["unexplained"], [])

  def test_startup_and_service_reach_a_loop_bound_connection(self):
    """The app's startup opens a connection to its service. The guard refuses it without
    `--service`, the node crashes without `--startup`, and with both every run reuses the
    connection on the startup's loop."""
    server = echo_server()
    port = server.server_address[1]
    try:
      with tempfile.TemporaryDirectory() as d:
        app = write_app(Path(d), SERVICE_APP)
        (app / "app" / "server.py").write_text(textwrap.dedent(SERVICE_STARTUP))
        env = ("--env", f"ECHO_PORT={port}", "--max-scripts", "1")
        bare = run_cli(app, *env)
        refused = run_cli(app, *env, "--startup", "app.server:startup")
        both = run_cli(app, *env, "--startup", "app.server:startup",
                       "--service", f"127.0.0.1:{port}")
    finally:
      server.shutdown()
      server.server_close()
    self.assertTrue(any("KeyError" in c for c in bare["crashes"]), bare)
    self.assertIn("startup: NetworkBlocked", " ".join(refused["errors"]))
    self.assertEqual((both["ran"], both["crashes"], both["errors"]), (True, {}, []))
    self.assertEqual(both["nodes_ran"], ["chat"])
    self.assertIn(f"--service 127.0.0.1:{port}", both["setup"])
    self.assertIn("--startup app.server:startup", both["setup"])

  def test_without_the_seam_the_flow_is_unexplained(self):
    """With the memory seam off, B's prompt still carries A's marker, which `unexplained`
    reports as a path the recorders missed."""
    with tempfile.TemporaryDirectory() as d:
      app = write_app(Path(d), CATALOGUE_APP.replace("__SEAM__", "mem"), "./app/graph.py:make_graph")
      s = run_cli(app, "--seams", "file,db,http")
    self.assertNotIn("chat@B", s["findings"])
    self.assertIn(["A", "built:make_graph", "chat@B"], s["unexplained"])


if __name__ == "__main__":
  unittest.main()
