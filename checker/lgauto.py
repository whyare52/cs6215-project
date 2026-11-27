"""Zero-config `lgtrace` run of a LangGraph app, with no per-app adapter.

`python -m lgauto <repo> [--graph NAME] [--env KEY=VAL]` finds the app's graphs, replaces every
model and tool by generic stand-ins, runs principals A, B, A on one store, and writes the spec,
the findings and the unexplained flows. Run it with the app's own venv, from `project/checker`.

What it does, in order
- Finds graphs. `langgraph.json` (or `aegra.json`, the same format) names graphs as
  `path.py:attr` or `module:attr`, with `env`, `dependencies` and `store.index`. Without one, it
  scans `.py` files that build a graph and takes module-level compiled graphs, builders and
  zero-argument factories. A graph may be compiled, a `StateGraph` builder, or a factory that
  takes the run config, sync or async. A factory is called per run, as the LangGraph server
  does, as external task `make_<graph>`, and the strings its graph holds are written to
  `built:<graph>` so `lgtrace.built_reads` sees prompts baked into it.
- Replaces every LLM. `BaseChatModel.__new__` returns an `AutoLLM`, so any provider class,
  `init_chat_model` and `create_agent(model="...")` get one. It copies the markers it sees.
  `bind_tools` and `with_structured_output` work. Structured output and tool arguments are
  built from their JSON schema, strings get the markers seen, and every enum, `Literal` and
  bool field is a decision. A tool-bound call decides which tool to call, or none, and after a
  tool result it replies. A plain reply decides between text and the JSON template the prompt
  shows, when it shows one. Embeddings are `DeterministicFakeEmbedding`.
- Stubs tools. `BaseTool.run` and `arun` run the real tool with the network blocked and, if it
  raises, return the markers of its input and a fresh result id (`--tools stub` always does).
  Sockets other than `AF_UNIX` refuse to connect and names do not resolve.
- Builds inputs from the graph's input schema. `messages` gets one user message, and each
  required text field the principal's marker. Ids get the principal's user id.
- Sets principals the standard way. Each run's config has `configurable.thread_id`,
  `user_id`, `langgraph_auth_user` and `langgraph_auth_user_id`, `metadata.owner`, and the
  graph's `context_schema` gets the same ids. Runs are A, B, A, with A's two runs in one thread.
- Answers interrupts. A LangGraph `HumanInterrupt` or a langchain `HITLRequest` is answered
  with each allowed response type as a decision, any other interrupt with plain text.
- Records what lgtrace records generically, the store, files under the run's work directory
  (a copy of the repo, `HOME` and `TMPDIR`) and `unexplained` flows. Threads and thread pools
  carry the context of the code that started them, so their work is attributed to its task.
- Explores decisions. Each script fixes some decisions, and every decision a script met but
  did not fix spawns one script per other option, as a tree, up to `--max-scripts`. Each script
  runs in a fresh worker process on a fresh copy of the repo, so no in-process cache or file
  carries over between scripts.

Setup flags, each counted as setup: `--graph`, `--env KEY=VAL`, `--path DIR` (extra import
root), `--tools stub`, `--principal-setter MODULE:FN`, `--service HOST:PORT` and `--startup
MODULE:ATTR`. `--service` lets the app's own clients open sockets to a running service, such as
its database, which the guard otherwise refuses. HTTP clients still get the fake service, and a
service keeps its state across scripts. `--startup` enters the app's startup (its server's
lifespan, say) once per worker before the graph loads, and then the probe and every run share
the startup's event loop.
"""

from __future__ import annotations

import argparse
import ast
import asyncio
import contextlib
import faulthandler
import contextvars
import dataclasses
import functools
import hashlib
import importlib
import importlib.util
import inspect
import json
import os
import pickle
import queue
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import types
import uuid
from collections import deque
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

PY_DIR = Path(__file__).resolve().parent
if str(PY_DIR) not in sys.path:
  sys.path.insert(0, str(PY_DIR))

import irspec  # noqa: E402
import lgseams  # noqa: E402
import lgtrace  # noqa: E402

CONFIG_NAMES = ("langgraph.json", "aegra.json")
SEAMS = ("memory", "file", "db", "http")
PRINCIPALS = ("A", "B")
ORDER = ("A", "B", "A")
ATTACKERS = ("A",)
MAX_SCRIPTS = 48
MAX_RESUMES = 10
RECURSION_LIMIT = 40
DRAIN_SECONDS = 90.0
DAEMON_SECONDS = 2.0
TIMER_CAP = 1.0
RUN_SECONDS = float(os.environ.get("LGAUTO_RUN_SECONDS", "240"))
WORKER_TIMEOUT = 1800
EMBED_DIMS = 1536
SKIP_DIRS = frozenset({".git", "node_modules", ".venv", "venv", "__pycache__", ".mypy_cache",
                       ".pytest_cache", ".ruff_cache", "web", "frontend", "dist", "build"})
TEST_PARTS = frozenset({"test", "tests", "testing"})
CODE_SUFFIXES = (".py", ".pyc", ".pyi", ".so", ".pth", ".typed")
GRAPH_CALLS = ("StateGraph(", "create_agent(", "create_react_agent(", "MessageGraph(",
               "create_deep_agent(")
FINISH_WORDS = frozenset({"done", "finish", "finished", "complete", "final", "submit", "end"})
OFFLINE_ENV = {"LANGCHAIN_TRACING_V2": "false", "LANGSMITH_TRACING": "false",
               "LANGFUSE_TRACING": "false", "ANONYMIZED_TELEMETRY": "False",
               "DO_NOT_TRACK": "1", "HF_HUB_OFFLINE": "1", "TRANSFORMERS_OFFLINE": "1"}
# Placeholder provider keys, so an app's import-time check for some key passes. No call can use
# them, since every model is an `AutoLLM` and the network is blocked.
PLACEHOLDER_KEYS = tuple(f"{p}_API_KEY" for p in (
  "OPENAI", "ANTHROPIC", "GOOGLE", "GEMINI", "GROQ", "DEEPSEEK", "MISTRAL", "TAVILY"))


# ---------------------------------------------------------------------------------------------
# Graph discovery


@dataclass(frozen=True)
class GraphRef:
  """One graph entry. `file` is a path below the config's directory, or `module` a dotted
  module, and `attr` the attribute holding the graph or its factory."""
  name: str
  attr: str
  file: str = ""
  module: str = ""


@dataclass(frozen=True)
class AppConfig:
  """What the config says, with paths relative to the repo. `config` is empty for a scan."""
  config: str
  base: str
  graphs: tuple[GraphRef, ...]
  env: Mapping[str, str] | str = field(default_factory=dict)
  dependencies: tuple[str, ...] = ()
  store_index: Mapping[str, Any] | None = None


def find_config(repo: Path) -> Path | None:
  """The shallowest `langgraph.json` (else `aegra.json`) in `repo`, outside skipped dirs."""
  for name in CONFIG_NAMES:
    found = sorted((p for p in repo.rglob(name) if not SKIP_DIRS & set(p.relative_to(repo).parts)
                    and len(p.relative_to(repo).parts) <= 3),
                   key=lambda p: (len(p.parts), str(p)))
    if found:
      return found[0]
  return None


def parse_graph(name: str, spec: Any) -> GraphRef:
  """`./a/b.py:attr` or `pkg.mod:attr`, or a dict with `path`."""
  target = spec.get("path", "") if isinstance(spec, Mapping) else str(spec)
  where, _, attr = target.rpartition(":")
  if where.endswith(".py") or "/" in where:
    return GraphRef(name, attr, file=os.path.normpath(where))
  return GraphRef(name, attr, module=where)


def parse_config(repo: Path, path: Path) -> AppConfig:
  data = json.loads(path.read_text())
  base = path.parent.relative_to(repo)
  graphs = tuple(parse_graph(n, s) for n, s in data.get("graphs", {}).items())
  deps = tuple(os.path.normpath(base / d) for d in data.get("dependencies", [])
               if isinstance(d, str) and d.startswith((".", "/")))
  index = (data.get("store") or {}).get("index")
  return AppConfig(str(path.relative_to(repo)), str(base), graphs, data.get("env") or {}, deps,
                   index)


def scan(repo: Path) -> AppConfig:
  """Candidate graphs of a repo without config: module-level names in files that build one.

  A name is a candidate when its assignment's value or its function body calls a graph builder
  or `.compile(`. Tests are skipped. Whether it really is a graph is decided on import."""
  graphs: list[GraphRef] = []
  for path in sorted(repo.rglob("*.py")):
    rel = path.relative_to(repo)
    if SKIP_DIRS & set(rel.parts) or TEST_PARTS & set(rel.parts) or rel.name.startswith("test_"):
      continue
    try:
      text = path.read_text(errors="replace")
    except OSError:
      continue
    if not any(c in text for c in GRAPH_CALLS):
      continue
    try:
      tree = ast.parse(text)
    except SyntaxError:
      continue
    for node in tree.body:
      src = ast.get_source_segment(text, node) or ""
      if not (any(c in src for c in GRAPH_CALLS) or ".compile(" in src):
        continue
      names: list[str] = []
      if isinstance(node, ast.Assign):
        names = [t.id for t in node.targets if isinstance(t, ast.Name)]
      elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
        names = [node.target.id]
      elif isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef):
        names = [node.name]
      elif isinstance(node, ast.ClassDef):
        names = [node.name if m.name == "__init__" else f"{node.name}.{m.name}"
                 for m in node.body if isinstance(m, ast.FunctionDef | ast.AsyncFunctionDef)
                 and any(c in (ast.get_source_segment(text, m) or "") for c in GRAPH_CALLS)]
      graphs.extend(GraphRef(f"{rel.with_suffix('').as_posix()}:{n}", n, file=str(rel))
                    for n in names if not n.startswith("_"))
  return AppConfig("", ".", tuple(graphs))


def app_config(repo: Path) -> AppConfig:
  path = find_config(repo)
  return parse_config(repo, path) if path else scan(repo)


def select(graphs: Sequence[GraphRef], wanted: Sequence[str]) -> list[GraphRef]:
  """The graphs named in `wanted` (by name or attr), or all of them."""
  if not wanted:
    return list(graphs)
  picked = [g for g in graphs if g.name in wanted or g.attr in wanted]
  if not picked:
    raise SystemExit(f"no graph {list(wanted)} among {[g.name for g in graphs]}")
  return picked


# ---------------------------------------------------------------------------------------------
# Environment


def parse_env_file(path: Path) -> dict[str, str]:
  """`KEY=VALUE` lines of a dotenv file, quotes stripped, comments and `export` ignored."""
  out: dict[str, str] = {}
  for line in path.read_text(errors="replace").splitlines():
    line = line.strip()
    if not line or line.startswith("#") or "=" not in line:
      continue
    key, _, value = line.removeprefix("export ").partition("=")
    value = value.strip()
    if value[:1] in "\"'" and value[-1:] == value[:1] and len(value) > 1:
      value = value[1:-1]
    else:
      value = value.split(" #", 1)[0].strip()
    out[key.strip()] = value
  return out


ENV_FILES = (".env", ".env.local", ".env.example", ".env.sample", ".env.template", ".env.dev",
             ".env.development")


def config_env(app: Path, cfg: AppConfig) -> dict[str, str]:
  """The config's `env`, a dict or a dotenv file, else the file's `.example` sibling. A config
  without `env`, or no config, takes the first dotenv file of `ENV_FILES` in its directory, the
  developer's convention."""
  if isinstance(cfg.env, Mapping) and cfg.env:
    return {k: str(v) for k, v in cfg.env.items()}
  if isinstance(cfg.env, Mapping):
    found = next((app / cfg.base / n for n in ENV_FILES if (app / cfg.base / n).is_file()), None)
    return parse_env_file(found) if found else {}
  path = app / cfg.base / cfg.env
  for candidate in (path, path.with_name(path.name + ".example")):
    if candidate.is_file():
      return parse_env_file(candidate)
  return {}


# ---------------------------------------------------------------------------------------------
# Network guard


class NetworkBlocked(ConnectionRefusedError):
  pass


LOCAL_NAMES = frozenset({"localhost", "127.0.0.1", "::1"})


def service_addresses(services: Iterable[str]) -> frozenset[tuple[str, int]]:
  """`HOST:PORT` strings as (host, port), with every local name standing for all of them."""
  out: set[tuple[str, int]] = set()
  for s in services:
    host, sep, port = s.strip().rpartition(":")
    if not sep or not port.isdigit():
      raise ValueError(f"--service wants HOST:PORT, got {s!r}")
    host = host.strip("[]")
    names = LOCAL_NAMES if host in LOCAL_NAMES else {host}
    out.update((h, int(port)) for h in names)
  return frozenset(out)


def block_network(services: Iterable[str] = ()) -> None:
  """Every socket but `AF_UNIX` refuses to connect, and no host name resolves, except the
  `--service` addresses, which the app's own clients reach as they are."""
  if getattr(socket, "_lgauto_blocked", False):
    return
  allowed = set(service_addresses(services))
  hosts = {h for h, _ in allowed}
  connect, connect_ex = socket.socket.connect, socket.socket.connect_ex
  getaddrinfo, create_connection = socket.getaddrinfo, socket.create_connection
  for host, port in list(allowed):  # a named host is reached at its addresses
    with contextlib.suppress(OSError):
      allowed.update((str(ai[4][0]), port) for ai in getaddrinfo(host, port))

  def open_to(self: socket.socket | None, address: Any) -> bool:
    if self is not None and self.family == getattr(socket, "AF_UNIX", None):
      return True
    return isinstance(address, tuple) and len(address) >= 2 and (
      (str(address[0]), int(address[1])) in allowed)

  def guarded_connect(self: socket.socket, address: Any) -> Any:
    if open_to(self, address):
      return connect(self, address)
    raise NetworkBlocked(f"lgauto: network disabled ({address!r})")

  def guarded_connect_ex(self: socket.socket, address: Any) -> int:
    if open_to(self, address):
      return connect_ex(self, address)
    return 111  # ECONNREFUSED

  def guarded_getaddrinfo(host: Any, *args: Any, **kwargs: Any) -> Any:
    if host in (None, "", *LOCAL_NAMES) or host in hosts:
      return getaddrinfo(host, *args, **kwargs)
    raise socket.gaierror(f"lgauto: network disabled ({host!r})")

  def guarded_create_connection(address: Any, *args: Any, **kwargs: Any) -> Any:
    if open_to(None, address):
      return create_connection(address, *args, **kwargs)
    raise NetworkBlocked(f"lgauto: network disabled ({address!r})")

  socket.socket.connect = guarded_connect  # type: ignore[method-assign]
  socket.socket.connect_ex = guarded_connect_ex  # type: ignore[method-assign]
  socket.getaddrinfo = guarded_getaddrinfo  # type: ignore[assignment]
  socket.create_connection = guarded_create_connection  # type: ignore[assignment]
  socket._lgauto_blocked = True  # type: ignore[attr-defined]


# ---------------------------------------------------------------------------------------------
# Decisions


@dataclass
class Current:
  """The worker's state: markers, the principal being served, the script's choices and every
  decision met so far with its options, in first-use order."""
  markers: dict[str, str] = field(default_factory=dict)
  principal: str = ""
  choices: dict[str, int] = field(default_factory=dict)
  used: dict[str, list[str]] = field(default_factory=dict)
  tools: str = "guarded"
  files: bool = True
  missing: list[str] = field(default_factory=list)
  env_missing: list[str] = field(default_factory=list)
  setter: Callable[[Any], Any] | None = None
  loop: AppLoop | None = None
  files_missing: list[str] = field(default_factory=list)
  stubbed: list[str] = field(default_factory=list)
  lock: Any = field(default_factory=threading.Lock)


CURRENT = Current()


def decide(point: str, options: Sequence[Any]) -> Any:
  """The script's choice among `options` at decision `point`, for the principal served."""
  if not options:
    raise ValueError(f"decision {point} has no options")
  key = f"{CURRENT.principal}|{point}"
  with CURRENT.lock:
    CURRENT.used.setdefault(key, [json.dumps(o, default=str) for o in options])
  return options[CURRENT.choices.get(key, 0) % len(options)]


def explore(run_script: Callable[[dict[str, int]], tuple[Any, Mapping[str, Sequence[str]]]],
            max_scripts: int) -> list[tuple[dict[str, int], Any, dict[str, list[str]]]]:
  """Scripts as a tree over decisions. A script runs with its choices, and every decision it
  met but did not fix spawns one child per other option, with the decisions met before it
  fixed to their default. A child whose decisions met and choices repeat an earlier script's
  is dropped. At most `max_scripts` scripts are kept."""
  frontier: deque[dict[str, int]] = deque([{}])
  seen: set[tuple[tuple[str, int], ...]] = set()
  kept: list[tuple[dict[str, int], Any, dict[str, list[str]]]] = []
  while frontier and len(kept) < max_scripts:
    choices = frontier.popleft()
    result, used = run_script(choices)
    sig = tuple(sorted((k, choices.get(k, 0)) for k in used))
    if sig in seen:
      continue
    seen.add(sig)
    kept.append((choices, result, {k: list(v) for k, v in used.items()}))
    fixed = dict(choices)
    for key, options in used.items():
      if key in choices:
        continue
      frontier.extend({**fixed, key: i} for i in range(1, len(options)))
      fixed[key] = 0
  return kept


# ---------------------------------------------------------------------------------------------
# Schema filling


def seen_text(value: Any) -> str:
  return " ".join(m for m in CURRENT.markers.values()
                  if any(m in t for t in lgtrace.leaves(value)))


def _deref(schema: Mapping[str, Any], defs: Mapping[str, Any]) -> Mapping[str, Any]:
  seen = 0
  while "$ref" in schema and seen < 20:
    schema = defs.get(schema["$ref"].rsplit("/", 1)[-1], {})
    seen += 1
  return schema


def fill_schema(schema: Mapping[str, Any], point: str, seen: str,
                defs: Mapping[str, Any] | None = None, depth: int = 0) -> Any:
  """A value of JSON schema `schema`. Strings carry `seen`, and each enum, const-free
  `Literal` and bool is decision `point.<path>`. Objects fill every property."""
  defs = {**(defs or {}), **schema.get("$defs", {}), **schema.get("definitions", {})}
  s = _deref(schema, defs)
  if depth > 8:
    return None
  if "const" in s:
    return s["const"]
  if "enum" in s and s["enum"]:
    return decide(point, list(s["enum"]))
  for key in ("anyOf", "oneOf"):
    if key in s:
      branches = [b for b in s[key] if _deref(b, defs).get("type") != "null"] or s[key]
      return fill_schema(branches[0], point, seen, defs, depth + 1)
  if "allOf" in s and s["allOf"]:
    return fill_schema(s["allOf"][0], point, seen, defs, depth + 1)
  kind = s.get("type")
  if isinstance(kind, list):
    kind = next((k for k in kind if k != "null"), "string")
  if kind is None and "properties" in s:
    kind = "object"
  match kind:
    case "boolean":
      return decide(point, [False, True])
    case "integer":
      return int(s.get("default", s.get("minimum", 1)) or 0)
    case "number":
      return float(s.get("default", s.get("minimum", 1.0)) or 0.0)
    case "array":
      items = s.get("items") or {"type": "string"}
      n = max(1, int(s.get("minItems", 1)))
      return [fill_schema(items, f"{point}[]", seen, defs, depth + 1) for _ in range(n)]
    case "object":
      props = s.get("properties") or {}
      if not props:
        return {} if s.get("additionalProperties") is False else {"text": text(seen, point)}
      return {k: fill_schema(v, f"{point}.{k}", seen, defs, depth + 1) for k, v in props.items()}
    case "null":
      return None
    case _:
      return text(seen, point)


_TEXTS = iter(range(1, 10**9))


def text(seen: str, point: str = "") -> str:
  """Generated text carrying `seen`, unique per call, so that text matching tells copies of one
  output apart from another output that saw the same markers."""
  leaf = point.rsplit(".", 1)[-1] if point else ""
  return f"[auto{' ' + leaf if leaf else ''} t{next(_TEXTS)}] {seen}".strip()


def schema_of(schema: Any) -> tuple[dict[str, Any], str]:
  """(JSON schema, name) of a pydantic model, TypedDict, dataclass, dict schema or tool."""
  if isinstance(schema, Mapping):
    if "function" in schema:
      fn = schema["function"]
      return dict(fn.get("parameters", {})), fn.get("name", "schema")
    if "parameters" in schema and "name" in schema:
      return dict(schema["parameters"]), schema["name"]
    if "input_schema" in schema and "name" in schema:
      return dict(schema["input_schema"]), schema["name"]
    return dict(schema), str(schema.get("title", "schema"))
  if isinstance(schema, type) and hasattr(schema, "model_json_schema"):
    return schema.model_json_schema(), schema.__name__
  try:
    from langchain_core.utils.function_calling import convert_to_openai_tool
    fn = convert_to_openai_tool(schema)["function"]
    return dict(fn.get("parameters", {})), fn.get("name", getattr(schema, "__name__", "tool"))
  except Exception:  # noqa: BLE001, fall back to type hints
    pass
  from pydantic import TypeAdapter
  return TypeAdapter(schema).json_schema(), getattr(schema, "__name__", "schema")


def build_value(schema: Any, point: str, seen: str) -> Any:
  """An instance of `schema` filled by `fill_schema`, validated when it is a pydantic model."""
  js, _ = schema_of(schema)
  value = fill_schema(js, point, seen)
  if isinstance(schema, type) and hasattr(schema, "model_validate"):
    try:
      return schema.model_validate(value)
    except Exception:  # noqa: BLE001, a model with validators gets what it accepts
      return schema.model_construct(**value) if isinstance(value, Mapping) else value
  return value


_RANGE = re.compile(r"(?<![\w.\"])-?\d+(?:\.\d+)?\s*-\s*(-?\d+(?:\.\d+)?)(?![\w.\"])")
_BOOLS = re.compile(r"\btrue\s*/\s*false\b|\bfalse\s*/\s*true\b")


def json_template(prompt: str) -> Any:
  """The last JSON object a prompt shows as its output format, read leniently, or None.

  `{{`/`}}` are unescaped, `true/false` read as true, a range `0.0-1.0` as its upper end, and
  `...` and trailing commas dropped."""
  text_ = prompt.replace("{{", "{").replace("}}", "}")
  best: Any = None
  depth, start = 0, -1
  for i, ch in enumerate(text_):
    if ch == "{":
      if depth == 0:
        start = i
      depth += 1
    elif ch == "}" and depth:
      depth -= 1
      if depth == 0 and start >= 0:
        block = text_[start:i + 1]
        block = _BOOLS.sub("true", block)
        block = _RANGE.sub(r"\1", block)
        block = re.sub(r",\s*\.\.\.\s*(?=[\]}])", "", block)
        block = re.sub(r",\s*(?=[\]}])", "", block)
        try:
          value = json.loads(block)
        except ValueError:
          continue
        if isinstance(value, dict) and value:
          best = value
  return best


def fill_template(value: Any, seen: str) -> Any:
  """A JSON template with each string replaced by the markers seen, or by the first of its
  `a|b|c` alternatives, and each list cut to its first item."""
  match value:
    case str() if "|" in value and " " not in value:
      return value.split("|")[0]
    case str():
      return text(seen)
    case Mapping():
      return {k: fill_template(v, seen) for k, v in value.items()}
    case list():
      return [fill_template(v, seen) for v in value[:1]]
    case _:
      return value


# ---------------------------------------------------------------------------------------------
# The generic chat model


def _node() -> str:
  """The LangGraph node the current call runs in, or `-`."""
  try:
    from langgraph.config import get_config
    meta = get_config().get("metadata", {})
  except Exception:  # noqa: BLE001, outside a graph
    return "-"
  return str(meta.get("langgraph_node", "-"))


def _tool_specs(tools: Any) -> list[dict[str, Any]]:
  """Each bound tool as `{"name", "parameters"}`."""
  specs: list[dict[str, Any]] = []
  for t in tools or []:
    try:
      js, name = schema_of(t)
    except Exception:  # noqa: BLE001, an unconvertible tool is still callable by name
      js, name = {}, getattr(t, "name", None) or getattr(t, "__name__", "tool")
    if isinstance(t, Mapping) and t.get("type") not in (None, "function"):
      name = t.get("name", name)  # a provider built-in tool such as web search
    specs.append({"name": name, "parameters": js})
  return specs


def _forced(tool_choice: Any, names: Sequence[str]) -> list[str] | None:
  """The tools a `tool_choice` forces, or None when a reply without tools is allowed."""
  if tool_choice in (None, "auto", "none", False):
    return None
  if tool_choice in ("any", "required", True):
    return list(names)
  if isinstance(tool_choice, Mapping):
    name = (tool_choice.get("function") or {}).get("name") or tool_choice.get("name")
    return [name] if name in names else list(names)
  return [tool_choice] if tool_choice in names else list(names)


def is_finish(name: str) -> bool:
  """Whether a tool name says it ends the loop, by its words (`Done`, `ResearchComplete`)."""
  return bool(FINISH_WORDS & {w.lower() for w in re.findall(r"[A-Z]?[a-z]+|[A-Z]+", name)})


def _last_is_tool(messages: Any) -> bool:
  """Whether the call follows a tool call of this turn: the last message is a tool result, or
  an AI message with tool calls comes after the last user message carrying a marker. The
  second case ends loops through human review, whose answers carry no marker."""
  from langchain_core.messages import AIMessage, HumanMessage, ToolMessage
  msgs = list(messages or [])
  if msgs and isinstance(msgs[-1], ToolMessage):
    return True
  users = [i for i, m in enumerate(msgs) if isinstance(m, HumanMessage) and seen_text(m)]
  start = users[-1] if users else 0
  return any(isinstance(m, AIMessage) and m.tool_calls for m in msgs[start:])


def _prompt_text(messages: Any) -> str:
  return "\n".join(t for m in messages or [] for t in lgtrace.leaves(getattr(m, "content", m)))


@functools.cache
def auto_llm_class() -> type:
  from langchain_core.language_models.chat_models import BaseChatModel
  from langchain_core.messages import AIMessage
  from langchain_core.outputs import ChatGeneration, ChatResult
  from langchain_core.runnables import RunnableLambda

  class AutoLLM(BaseChatModel):
    """Every chat model of the app. It copies the markers it sees and decides tool calls,
    structured fields and reply formats through `decide`."""
    origin: str = ""

    @property
    def _llm_type(self) -> str:
      return "lgauto"

    def _record(self, value: Any) -> str:
      lgtrace.RESOURCES.add_call(lgtrace.LLMCall(lgtrace.current_task(),
                                                 lgtrace._snapshot(value), lgtrace.tick()))
      lgseams.MEMORY.task_end(value)
      return seen_text(value)

    def reply(self, messages: Any, tools: Any = None, tool_choice: Any = None) -> AIMessage:
      seen = self._record(messages)
      node = _node()
      specs = _tool_specs(tools)
      names = [s["name"] for s in specs]
      calls: list[dict[str, Any]] = []
      if specs:
        forced = _forced(tool_choice, names)
        if _last_is_tool(messages):
          finish = [n for n in (forced or []) if is_finish(n)]
          pick = (finish or forced or [None])[0]
        else:
          pick = decide(f"{node}.tool", forced or [None, *names])
        if pick is not None:
          spec = next(s for s in specs if s["name"] == pick)
          args = fill_schema(spec["parameters"] or {"type": "object"}, f"{node}.{pick}", seen)
          calls = [{"name": pick, "args": args if isinstance(args, dict) else {},
                    "id": f"call_{uuid.uuid4().hex[:8]}"}]
      content = text(seen)
      if not calls:
        template = json_template(_prompt_text(messages))
        if template is not None and decide(f"{node}.format", ["text", "json"]) == "json":
          content = json.dumps(fill_template(template, seen), ensure_ascii=False)
      return AIMessage(content=content, tool_calls=calls)

    def _generate(self, messages, stop=None, run_manager=None, **kwargs) -> ChatResult:
      tools = kwargs.get("tools") or kwargs.get("functions")
      message = self.reply(messages, tools, kwargs.get("tool_choice"))
      return ChatResult(generations=[ChatGeneration(message=message)])

    async def _agenerate(self, messages, stop=None, run_manager=None, **kwargs) -> ChatResult:
      return self._generate(messages, stop, None, **kwargs)

    def bind_tools(self, tools, *, tool_choice=None, **kwargs):
      """Tools bound in OpenAI format, as provider models bind them, which libraries such as
      langgraph-supervisor inspect."""
      from langchain_core.utils.function_calling import convert_to_openai_tool

      def convert(t: Any) -> Any:
        try:
          return convert_to_openai_tool(t)
        except Exception:  # noqa: BLE001, a provider built-in tool is kept as given
          return t
      return self.bind(tools=[convert(t) for t in tools], tool_choice=tool_choice)

    def with_structured_output(self, schema, *, include_raw: bool = False, **kwargs):
      _, name = schema_of(schema)

      def run(value: Any, **bound: Any) -> Any:  # `.bind(tool_choice=...)` lands in `bound`
        seen = self._record(value)
        out = build_value(schema, f"{_node()}.{name}", seen)
        if not include_raw:
          return out
        raw = AIMessage(content="", tool_calls=[{
          "name": name, "args": out.model_dump() if hasattr(out, "model_dump") else out,
          "id": f"call_{uuid.uuid4().hex[:8]}"}])
        return {"raw": raw, "parsed": out, "parsing_error": None}
      return RunnableLambda(run, name=f"structured_{name}")

    def get_num_tokens(self, text: str) -> int:
      return max(1, len(str(text)) // 4)

    def get_num_tokens_from_messages(self, messages, tools=None) -> int:
      return sum(self.get_num_tokens(_prompt_text([m])) for m in messages)

  return AutoLLM


def install_models() -> None:
  """Every `BaseChatModel` construction returns an `AutoLLM`, `init_chat_model` builds one
  without importing a provider, and every `Embeddings` is a deterministic fake."""
  from langchain_core.language_models.chat_models import BaseChatModel
  auto = auto_llm_class()

  def chat_new(cls: type, *args: Any, **kwargs: Any) -> Any:
    if issubclass(cls, auto):
      return object.__new__(cls)
    return auto(origin=cls.__name__)
  BaseChatModel.__new__ = staticmethod(chat_new)  # type: ignore[assignment]

  with contextlib.suppress(ImportError):
    from langchain_core.embeddings import DeterministicFakeEmbedding, Embeddings

    def embed_new(cls: type, *args: Any, **kwargs: Any) -> Any:
      if issubclass(cls, DeterministicFakeEmbedding):
        return object.__new__(cls)
      return DeterministicFakeEmbedding(size=EMBED_DIMS)
    Embeddings.__new__ = staticmethod(embed_new)  # type: ignore[assignment]

  with contextlib.suppress(ImportError):
    import langchain.chat_models.base as chat_base
    if hasattr(chat_base, "_init_chat_model_helper"):
      chat_base._init_chat_model_helper = lambda model=None, **kw: auto(origin=str(model))
    with contextlib.suppress(ImportError, AttributeError):
      import langchain.embeddings.base as embed_base
      from langchain_core.embeddings import DeterministicFakeEmbedding as Fake
      embed_base.init_embeddings = lambda *a, **k: Fake(size=EMBED_DIMS)


# ---------------------------------------------------------------------------------------------
# Tools


def _is_bubble(e: BaseException) -> bool:
  """LangGraph's control-flow exceptions (interrupts, parent commands) pass through."""
  return any(c.__name__ in ("GraphBubbleUp", "GraphInterrupt", "NodeInterrupt", "ParentCommand")
             for c in type(e).__mro__)


def install_tools() -> None:
  """`BaseTool.run`/`arun` run the real tool, which cannot reach the network, and return a stub
  carrying the markers of the input when it raises or when tools are `stub`."""
  from langchain_core.messages import ToolMessage
  from langchain_core.tools import BaseTool
  run, arun = BaseTool.run, BaseTool.arun

  def stub(self: BaseTool, tool_input: Any, kwargs: Mapping[str, Any], why: str) -> Any:
    with CURRENT.lock:
      CURRENT.stubbed.append(f"{self.name}: {why}"[:200])
    content = f"[tool {self.name}] {seen_text(tool_input)} result-{uuid.uuid4().hex[:8]}"
    call_id = kwargs.get("tool_call_id")
    if call_id is None and isinstance(tool_input, Mapping):
      call_id = tool_input.get("id") if tool_input.get("type") == "tool_call" else None
    return ToolMessage(content=content, tool_call_id=call_id, name=self.name) if call_id \
      else content

  def guarded(self: BaseTool, tool_input: Any, *args: Any, **kwargs: Any) -> Any:
    lgseams.MEMORY.task_end(tool_input)
    if CURRENT.tools == "stub":
      return stub(self, tool_input, kwargs, "stub")
    try:
      return run(self, tool_input, *args, **kwargs)
    except Exception as e:  # noqa: BLE001, a failing real tool becomes a stub
      if _is_bubble(e):
        raise
      return stub(self, tool_input, kwargs, f"{type(e).__name__}: {e}")

  async def aguarded(self: BaseTool, tool_input: Any, *args: Any, **kwargs: Any) -> Any:
    lgseams.MEMORY.task_end(tool_input)
    if CURRENT.tools == "stub":
      return stub(self, tool_input, kwargs, "stub")
    try:
      return await arun(self, tool_input, *args, **kwargs)
    except Exception as e:  # noqa: BLE001
      if _is_bubble(e):
        raise
      return stub(self, tool_input, kwargs, f"{type(e).__name__}: {e}")

  BaseTool.run = guarded  # type: ignore[method-assign]
  BaseTool.arun = aguarded  # type: ignore[method-assign]


# ---------------------------------------------------------------------------------------------
# Graphs, threads


def graph_nodes(builder: Any) -> frozenset[str]:
  return frozenset(n for n in getattr(builder, "nodes", {}) if n not in ("__start__", "__end__"))


def static_nodes(graph: Any, depth: int = 0) -> set[str]:
  """Nodes of a compiled graph and of the compiled subgraphs that are its nodes."""
  builder = getattr(graph, "builder", None)
  out = set(graph_nodes(builder))
  for spec in getattr(builder, "nodes", {}).values() if depth < 5 else ():
    inner = getattr(spec, "runnable", None)
    inner = getattr(inner, "inner", inner)
    if hasattr(inner, "builder") and is_compiled(inner):
      out |= static_nodes(inner, depth + 1)
  return out


@dataclass
class Registry:
  """The node sets of every graph compiled in the worker."""
  graphs: set[frozenset[str]] = field(default_factory=set)

  def add(self, builder: Any, name: str | None) -> None:
    if nodes := graph_nodes(builder):
      self.graphs.add(nodes)


REGISTRY = Registry()


def install_compile() -> None:
  """`StateGraph.compile` compiles `lgtrace.instrument(self)`, so every graph the app builds,
  subgraphs called from inside nodes too, records its reads."""
  from langgraph.graph.state import StateGraph
  compile_ = StateGraph.compile

  @functools.wraps(compile_)
  def compile(self: Any, *args: Any, **kwargs: Any) -> Any:
    if getattr(self, "_lgauto_instrumented", False):
      graph = compile_(self, *args, **kwargs)
    else:
      inst = lgtrace.instrument(self)
      inst._lgauto_instrumented = True
      graph = compile_(inst, *args, **kwargs)
    REGISTRY.add(self, kwargs.get("name") or getattr(graph, "name", None))
    return graph
  StateGraph.compile = compile  # type: ignore[method-assign]


def built_strings(obj: Any, limit: int = 4000) -> list[str]:
  """Strings a built graph holds in node runnables, bound fields and closures, deduplicated."""
  out: dict[str, None] = {}
  stack, seen = [obj], set()
  while stack and len(seen) < limit:
    x = stack.pop()
    if id(x) in seen or isinstance(x, int | float | bool | type(None) | type):
      continue
    seen.add(id(x))
    if isinstance(x, str):
      out.setdefault(x)
      continue
    if isinstance(x, bytes | bytearray) or inspect.ismodule(x):
      continue
    if isinstance(x, Mapping):
      stack.extend(x.values())
    elif isinstance(x, list | tuple | set | frozenset):
      stack.extend(x)
    if inspect.isfunction(x) or inspect.ismethod(x):
      fn = getattr(x, "__func__", x)
      stack.extend(c.cell_contents for c in fn.__closure__ or () if _filled(c))
      stack.append(getattr(x, "__self__", None))
      continue
    if isinstance(x, functools.partial):
      stack.extend([x.func, *x.args, *x.keywords.values()])
      continue
    with contextlib.suppress(Exception):
      stack.extend(vars(x).values())
  return list(out)


def _filled(cell: Any) -> bool:
  try:
    cell.cell_contents
  except ValueError:
    return False
  return True


# ---------------------------------------------------------------------------------------------
# Loading


def add_path(path: Path) -> None:
  if path.is_dir() and str(path) not in sys.path:
    sys.path.insert(0, str(path))


def package_root(file: Path) -> tuple[Path, str]:
  """The import root of `file` and its dotted module name, through `__init__.py` parents."""
  parts = [file.stem]
  d = file.parent
  while (d / "__init__.py").exists():
    parts.insert(0, d.name)
    d = d.parent
  return d, ".".join(parts)


def source_roots(app: Path, cfg: AppConfig, extra: Sequence[str]) -> list[Path]:
  """Import roots, the config's directory, its dependencies, their `src/` dirs and every
  `packages/*` workspace member, plus `extra`."""
  roots = [app / cfg.base, *(app / d for d in cfg.dependencies), *(app / e for e in extra)]
  roots += [r / "src" for r in roots]
  roots += [m.parent for r in list(roots) for m in r.glob("packages/*/*/__init__.py")]
  return [r for r in dict.fromkeys(roots) if r.is_dir()]


def find_module_dir(app: Path, name: str) -> Path | None:
  """The parent directory of the shallowest package or module `name` in the app."""
  hits = [p for p in (*app.rglob(f"{name}/__init__.py"), *app.rglob(f"{name}.py"))
          if not SKIP_DIRS & set(p.relative_to(app).parts)]
  if not hits:
    hits = [p for p in app.rglob(name) if p.is_dir() and not SKIP_DIRS & set(
      p.relative_to(app).parts) and any(p.glob("*.py"))]
    return min(hits, key=lambda p: len(p.parts)).parent if hits else None
  best = min(hits, key=lambda p: len(p.parts))
  return best.parent.parent if best.name == "__init__.py" else best.parent


class _StubMeta(type):
  """Every attribute of a stub class is another stub class, so `from x import A`, `A(...)`,
  `A.b.c()` and `class B(A)` all work."""

  def __getattr__(cls, name: str) -> Any:
    if name.startswith("_"):  # dunders and private hooks (`_abc_impl`) stay missing
      raise AttributeError(name)
    return _stub_class(f"{cls.__name__}.{name}")


class _Stub(metaclass=_StubMeta):
  def __init__(self, *args: Any, **kwargs: Any) -> None:
    pass

  def __getattr__(self, name: str) -> Any:
    if name.startswith("_"):
      raise AttributeError(name)
    return _stub_class(f"{type(self).__name__}.{name}")()

  def __call__(self, *args: Any, **kwargs: Any) -> Any:
    return _stub_class(f"{type(self).__name__}()")()

  def __iter__(self) -> Iterator[Any]:
    return iter(())

  def __bool__(self) -> bool:
    return False

  def __enter__(self) -> Any:
    return self

  def __exit__(self, *exc: Any) -> None:
    return None

  async def __aenter__(self) -> Any:
    return self

  async def __aexit__(self, *exc: Any) -> None:
    return None

  def __await__(self) -> Iterator[Any]:
    if False:  # noqa: SIM108, a generator that returns the stub itself
      yield
    return self

  def __getitem__(self, key: Any) -> Any:
    return _stub_class("item")()

  def __str__(self) -> str:
    return ""


def _stub_class(name: str) -> type:
  return _StubMeta(name.rsplit(".", 1)[-1] or "Stub", (_Stub,), {"__qualname__": name})


class _StubModule(type(sys)):
  """A missing module. Its `init_chat_model` still builds an `AutoLLM`, since that is the
  standard model factory every LLM is replaced through."""

  def __getattr__(self, name: str) -> Any:
    if name.startswith("_"):
      raise AttributeError(name)
    if name == "init_chat_model":
      return lambda model=None, **kw: auto_llm_class()(origin=str(model))
    return _stub_class(f"{self.__name__}.{name}")


class _StubFinder:
  """Imports any module below a stubbed root as a `_StubModule`."""
  roots: set[str] = set()

  @classmethod
  def find_spec(cls, name: str, path: Any = None, target: Any = None) -> Any:
    if name.split(".")[0] not in cls.roots:
      return None
    return importlib.util.spec_from_loader(name, cls, is_package=True)

  @staticmethod
  def create_module(spec: Any) -> Any:
    mod = _StubModule(spec.name)
    mod.__path__ = []
    return mod

  @staticmethod
  def exec_module(module: Any) -> None:
    pass


STUBBED_MODULES: list[str] = []


def stub_module(root: str) -> None:
  """Make `root` and every module below it a stub. Used for third-party client libraries the
  venv lacks, such as a mail or cloud SDK, whose calls then do nothing."""
  if _StubFinder not in sys.meta_path:
    sys.meta_path.insert(0, _StubFinder)  # type: ignore[arg-type]
  _StubFinder.roots.add(root)
  STUBBED_MODULES.append(root)


def import_resolving(app: Path, module: str, tries: int = 16) -> Any:
  """Import `module`. A missing first-party module gets the app directory that holds it on
  `sys.path`, and a missing third-party one becomes a stub (`stub_module`), then it retries."""
  added: list[str] = []
  for _ in range(tries):
    try:
      return importlib.import_module(module)
    except ModuleNotFoundError as e:
      missing = (e.name or "").split(".")[0]
      if not missing:
        raise
      where = find_module_dir(app, missing)
      if where is not None and str(where) not in sys.path:
        added.append(str(where))
        sys.path.insert(0, str(where))
      elif missing not in _StubFinder.roots and missing != module.split(".")[0]:
        stub_module(missing)
      else:
        raise
      for m in [m for m in sys.modules if m == missing or m.startswith(missing + ".")
                or m == module or m.startswith(module.split(".")[0] + ".")]:
        del sys.modules[m]
  raise ImportError(f"could not import {module} after adding {added}")


def load_attr(app: Path, cfg: AppConfig, ref: GraphRef) -> Any:
  if ref.file:
    file = (app / cfg.base / ref.file).resolve()
    root, module = package_root(file)
    add_path(root)
  else:
    module = ref.module
  try:
    obj = import_resolving(app, module)
  except ImportError as e:
    if not (ref.file and "relative import" in str(e)):
      raise
    # a module of a namespace package (a `src/` without `__init__.py`) imports from the app root
    base = (app / cfg.base).resolve()
    add_path(base)
    obj = import_resolving(app, ".".join(file.relative_to(base).with_suffix("").parts))
  for part in ref.attr.split("."):
    obj = getattr(obj, part)
  return obj


def is_compiled(obj: Any) -> bool:
  from langgraph.pregel import Pregel
  return isinstance(obj, Pregel)


def is_builder(obj: Any) -> bool:
  from langgraph.graph.state import StateGraph
  return isinstance(obj, StateGraph)


async def _maybe_await(x: Any) -> Any:
  while inspect.isawaitable(x):
    x = await x
  return x


def factory_arg(param: inspect.Parameter, config: Mapping[str, Any]) -> Any:
  """What the LangGraph server passes a factory parameter: the run config, or for `runtime`
  a `ServerRuntime`-like object with the run's user, whose `context` is a stub, falsy and
  with stub attributes, standing for the request's context."""
  ann = str(param.annotation)
  if param.name == "runtime" or "Runtime" in ann:
    conf = config.get("configurable", {})
    return types.SimpleNamespace(user=conf.get("langgraph_auth_user"), store=None,
                                 context=_stub_class("context")(),
                                 access_context="threads.create_run", execution_runtime=None)
  return dict(config)


async def call_factory(fn: Callable[..., Any], config: Mapping[str, Any]) -> Any:
  """Call a graph factory as the LangGraph server does, with the config when it takes one.
  A class is instantiated first and a context manager entered (and left open)."""
  if inspect.isclass(fn):  # a class that builds its graph in `__init__` and keeps it
    inst = fn()
    found = [v for v in vars(inst).values() if is_compiled(v) or is_builder(v)]
    if not found:
      raise TypeError(f"{fn.__name__}() holds no graph")
    return found[0]
  if hasattr(fn, "__qualname__") and "." in fn.__qualname__ and not inspect.ismethod(fn):
    owner = getattr(sys.modules.get(fn.__module__), fn.__qualname__.split(".")[0], None)
    if inspect.isclass(owner):
      fn = getattr(owner(), fn.__name__)
  params = [p for p in inspect.signature(fn).parameters.values()
            if p.default is p.empty and p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD,
                                                   p.KEYWORD_ONLY)]
  args = {p.name: factory_arg(p, config) for p in params}
  out = fn(**args)
  if hasattr(out, "__aenter__"):
    out = await out.__aenter__()
  elif hasattr(out, "__enter__") and not is_compiled(out):
    out = out.__enter__()
  return await _maybe_await(out)


# ---------------------------------------------------------------------------------------------
# Runs


@dataclass(frozen=True)
class AuthUser:
  """The `langgraph_auth_user` the LangGraph server passes, a `BaseUser` with dict access."""
  identity: str
  display_name: str
  permissions: tuple[str, ...] = ()
  is_authenticated: bool = True

  def __getitem__(self, key: str) -> Any:
    return getattr(self, key)

  def __contains__(self, key: str) -> bool:
    return hasattr(self, key)

  def __iter__(self) -> Iterator[str]:
    return iter(("identity", "display_name", "permissions", "is_authenticated"))

  def get(self, key: str, default: Any = None) -> Any:
    return getattr(self, key, default)


@dataclass(frozen=True)
class Principal:
  """What `--principal-setter` is called with: a user with the common id attribute names."""
  id: str

  @property
  def user_id(self) -> str:
    return self.id

  @property
  def identity(self) -> str:
    return self.id

  @property
  def name(self) -> str:
    return self.id

  def __getitem__(self, key: str) -> Any:
    return getattr(self, key)


def user_id(principal: str) -> str:
  return f"user-{principal}"


def run_config(principal: str, thread: str, graph_name: str) -> dict[str, Any]:
  uid = user_id(principal)
  return {"configurable": {"thread_id": thread, "user_id": uid, "langgraph_auth_user_id": uid,
                           "langgraph_auth_user": AuthUser(uid, f"User {principal}"),
                           "assistant_id": graph_name},
          "metadata": {"owner": uid, "user_id": uid},
          "recursion_limit": RECURSION_LIMIT}


def input_schema(graph: Any) -> dict[str, Any]:
  for get in (lambda: graph.get_input_jsonschema(),
              lambda: graph.input_schema.model_json_schema(),
              lambda: graph.get_input_schema().model_json_schema(),
              lambda: graph.input_schema.schema()):
    with contextlib.suppress(Exception):
      js = get()
      if isinstance(js, Mapping):
        return dict(js)
  return {}


def _texty(schema: Mapping[str, Any], defs: Mapping[str, Any]) -> bool:
  s = _deref(schema, defs)
  if s.get("type") == "string":
    return True
  return any(_texty(b, defs) for b in s.get("anyOf", []))


def fill_input(schema: Mapping[str, Any], principal: str, marker: str,
               keys: Sequence[str] = ()) -> dict[str, Any]:
  """An input of the graph's input schema. `messages` gets one user message and each picked
  field a value carrying `marker`, ids the user id. Required fields and `messages` are picked,
  or every text field when there are none."""
  defs = {**schema.get("$defs", {}), **schema.get("definitions", {})}
  props: Mapping[str, Any] = schema.get("properties", {}) or {}
  required = set(schema.get("required", []))
  picked = [k for k in props if k in required or k == "messages"]
  picked = picked or [k for k, v in props.items() if _texty(v, defs)]
  words = f"I am user {principal}. {marker}"
  if not props:
    return {"messages": [{"role": "user", "content": words}]}

  def value(name: str, s: Mapping[str, Any], depth: int = 0) -> Any:
    s = _deref(s, defs)
    if name == "messages":
      return [{"role": "user", "content": words}]
    for key in ("anyOf", "oneOf"):
      if key in s:
        branches = [b for b in s[key] if _deref(b, defs).get("type") != "null"] or s[key]
        return value(name, branches[0], depth + 1)
    kind = s.get("type")
    if "enum" in s:
      return s["enum"][0]
    if kind == "string" or kind is None and "properties" not in s:
      return user_id(principal) if re.search(r"(^|_)id$", name) else f"{name} of {words}"
    if kind == "array":
      return [value(name, s.get("items") or {"type": "string"}, depth + 1)]
    if kind == "object" or "properties" in s:
      inner = s.get("properties") or {}
      if not inner or depth > 4:
        return {"content": f"{name} of {words}", **{k: value(k, {}, depth + 1) for k in keys}}
      return {k: value(k, v, depth + 1) for k, v in inner.items()}
    if kind == "boolean":
      return False
    if kind in ("integer", "number"):
      return 0
    return f"{name} of {words}"
  out = {k: value(k, props[k]) for k in picked}
  free = any(isinstance(v, dict) and "content" in v for v in out.values())
  return out if free else {**{k: value(k, {}) for k in keys if k not in out}, **out}


class Ids(dict):
  """The run's ids as a dict whose keys are also attributes, since app code reads an
  undeclared context both ways (`ctx["thread_id"]`, `getattr(ctx, "thread_id", None)`)."""

  def __getattr__(self, name: str) -> Any:
    try:
      return self[name]
    except KeyError:
      raise AttributeError(name) from None


def factory_context_schema(fn: Any) -> type | None:
  """The `context_schema` class that a factory method's class declares, the schema an app
  that builds graphs from agent classes passes at run time when the graph declares none."""
  owner = getattr(fn, "__self__", None)
  if owner is None and "." in getattr(fn, "__qualname__", ""):
    owner = getattr(sys.modules.get(getattr(fn, "__module__", "")),
                    fn.__qualname__.split(".")[0], None)
  schema = getattr(owner, "context_schema", None)
  return schema if inspect.isclass(schema) else None


def init_names(schema: Any) -> set[str]:
  """The keyword parameters `schema(...)` names, or none when it takes `**kwargs` or has no
  readable signature."""
  try:
    params = inspect.signature(schema).parameters.values()
  except (TypeError, ValueError):
    return set()
  if any(p.kind is p.VAR_KEYWORD for p in params):
    return set()
  return {p.name for p in params if p.kind in (p.POSITIONAL_OR_KEYWORD, p.KEYWORD_ONLY)}


def context_for(graph: Any, principal: str, thread: str, fallback: type | None = None) -> Any:
  """The run context the LangGraph server passes: the graph's `context_schema` (else
  `fallback`) filled with the run's ids, or the ids as an `Ids` dict when there is no schema."""
  schema = getattr(graph, "context_schema", None) or fallback
  ids = Ids(user_id=user_id(principal), thread_id=thread, run_id=uuid.uuid4().hex,
            assistant_id="lgauto")
  if schema is None:
    return ids
  try:
    js, _ = schema_of(schema)
    names = set(js.get("properties", {}))
  except Exception:  # noqa: BLE001, no pydantic: the constructor's named parameters
    names = init_names(schema) or set(ids)
  values = {k: v for k, v in ids.items() if k in names}
  if isinstance(schema, type) and not issubclass(schema, Mapping) and hasattr(schema, "__init__"):
    with contextlib.suppress(Exception):
      return schema(**values)
  return values


_ENV_MESSAGE = re.compile(r"\b([A-Z][A-Z0-9_]{2,})\b[^.\n]{0,40}\b(?:env(?:ironment)?\b|must be set)"
                          r"|\b(?:env(?:ironment)? var(?:iable)?|set)\s+`?([A-Z][A-Z0-9_]{2,})")


_FILE_NAME = re.compile(r"[\w.-]+\.(?:ya?ml|json|toml|ini|cfg|conf|env)\b")


def example_for(app: Path, name: str) -> tuple[str, str] | None:
  """(example, target) paths below the app for a missing config file `name`: its
  `.example`, `.sample` or `.template` sibling anywhere in the app, copied beside itself."""
  stem, dot, ext = name.rpartition(".")
  variants = [f"{name}.{v}" for v in ("example", "sample", "template", "dist")]
  variants += [f"{stem}.{v}.{ext}" for v in ("example", "sample", "template")] if dot else []
  variants += [f"example.{name}", f"{stem}_example.{ext}" if dot else f"{name}_example"]
  for v in variants:
    hits = sorted((p for p in app.rglob(v) if not SKIP_DIRS & set(p.relative_to(app).parts)),
                  key=lambda p: len(p.parts))
    if hits:
      rel = hits[0].relative_to(app)
      return str(rel), str(rel.with_name(Path(name).name))
  return None


def learn_from(e: BaseException) -> None:
  """What a crash says the run lacked: an input key (a `KeyError` in app code) or an
  environment variable (a `KeyError` from `os.environ`, or a message naming one)."""
  frames = traceback.extract_tb(e.__traceback__)
  from_environ = bool(frames) and Path(frames[-1].filename).name in ("os.py", "<frozen os>")
  if isinstance(e, KeyError) and e.args and isinstance(e.args[0], str):
    (CURRENT.env_missing if from_environ else CURRENT.missing).append(e.args[0])
    return
  for m in _ENV_MESSAGE.finditer(str(e)):
    CURRENT.env_missing.append(m.group(1) or m.group(2))
  if isinstance(e, FileNotFoundError):
    names = [getattr(e, "filename", None) or "", *_FILE_NAME.findall(str(e))]
    CURRENT.files_missing.extend(Path(os.fsdecode(n)).name for n in names if n)


def crash_site(e: BaseException, app: Path) -> str:
  frames = traceback.extract_tb(e.__traceback__)
  inside = [f for f in frames if str(f.filename).startswith(str(app))] or frames[-1:]
  if not inside:
    return f"{type(e).__name__}: {str(e)[:200]}"
  f = inside[-1]
  try:
    where = Path(f.filename).relative_to(app)
  except ValueError:
    where = Path(f.filename).name
  return f"{type(e).__name__} at {where}:{f.lineno}: {str(e)[:200]}"


def human_answer(value: Any, point: str) -> Any:
  """A resume value for an interrupt, deciding the response type where the request lists the
  allowed ones (LangGraph's `HumanInterrupt`, langchain's `HITLRequest`)."""
  if isinstance(value, Sequence) and value and isinstance(value[0], Mapping) \
      and "action_request" in value[0]:
    req = value[0]
    allowed = [k.removeprefix("allow_") for k, v in (req.get("config") or {}).items()
               if k.startswith("allow_") and v] or ["accept"]
    kind = decide(f"{point}.human", ["respond" if k == "respond" else k for k in allowed])
    args = {"accept": None, "ignore": None, "respond": "Please keep it short.",
            "edit": dict(req.get("action_request") or {})}.get(kind)
    return [{"type": "response" if kind == "respond" else kind, "args": args}]
  if isinstance(value, Mapping) and "action_requests" in value:
    configs = {c.get("action_name"): c for c in value.get("review_configs", [])}
    decisions = []
    for req in value["action_requests"]:
      allowed = (configs.get(req.get("name")) or {}).get("allowed_decisions") or ["approve"]
      kind = decide(f"{point}.{req.get('name')}.human", list(allowed))
      d: dict[str, Any] = {"type": kind}
      if kind == "edit":
        d["edited_action"] = {"name": req.get("name"), "args": req.get("args", {})}
      if kind == "reject":
        d["message"] = "Please do not."
      decisions.append(d)
    return {"decisions": decisions}
  return "Please keep it short."


@dataclass
class Entry:
  """One script's server for one graph. `stream` serves one run like the LangGraph server: it
  builds the graph for the run when the entry is a factory, streams it on an event loop in a
  thread, answers interrupts, waits for background work, and keeps app crashes."""
  ref: GraphRef
  obj: Any
  store: Any
  saver: Any
  app: Path
  work: Path
  crashes: list[str] = field(default_factory=list)
  graph: Any = None

  async def build(self, config: Mapping[str, Any]) -> Any:
    if is_compiled(self.obj):
      return lgtrace.instrument_compiled(self.obj, checkpointer=self.saver, store=self.store)
    if is_builder(self.obj):
      return self.obj.compile(checkpointer=self.saver, store=self.store)
    with lgtrace.acting(f"make_{self.ref.attr.split('.')[-1]}"):
      out = await call_factory(self.obj, config)
      if is_builder(out):
        out = out.compile()
      if not is_compiled(out):
        raise TypeError(f"{self.ref.name} gave {type(out).__name__}, not a graph")
      strings = built_strings(out)
      lgseams.MEMORY.task_end(strings)
      lgtrace.emit(f"{lgtrace.BUILT_PREFIX}{self.ref.attr}", "write", strings)
    return lgtrace.instrument_compiled(out, checkpointer=self.saver, store=self.store)

  async def serve(self, inp: Any, config: dict[str, Any], kwargs: Mapping[str, Any],
                  out: queue.SimpleQueue[Any]) -> None:
    from langgraph.types import Command
    if CURRENT.setter is not None:  # `--principal-setter`, setup for apps keyed outside config
      CURRENT.setter(Principal(config["configurable"]["user_id"]))
    graph = await self.build(config)
    self.graph = graph
    accepted = inspect.signature(graph.astream).parameters
    extra = dict(kwargs)
    context = context_for(graph, config["metadata"]["owner"].removeprefix("user-"),
                          config["configurable"]["thread_id"], factory_context_schema(self.obj))
    if context is not None and "context" in accepted:
      extra["context"] = context
    value: Any = inp
    for _ in range(MAX_RESUMES + 1):
      async for ev in graph.astream(value, config, **extra):
        out.put(ev)
      try:
        state = await graph.aget_state(config, subgraphs=True)
      except Exception:  # noqa: BLE001, a graph without checkpointer cannot be resumed
        return
      pending = [(t.name, i) for t in state.tasks for i in getattr(t, "interrupts", ())]
      if not pending:
        return
      name, intr = pending[0]
      value = Command(resume=human_answer(intr.value, name))
    self.crashes.append(f"more than {MAX_RESUMES} interrupts")

  def stream(self, inp: Any, config: Any, **kwargs: Any) -> Iterator[Any]:
    out: queue.SimpleQueue[Any] = queue.SimpleQueue()
    done = object()
    before = set(threading.enumerate())

    loops: list[asyncio.AbstractEventLoop] = []
    shared = CURRENT.loop

    def loop() -> None:
      async def main() -> None:
        loops.append(asyncio.get_running_loop())
        older = asyncio.all_tasks()  # on a shared loop, the startup's own background tasks
        try:
          await self.serve(inp, dict(config), kwargs, out)
        except Exception as e:  # noqa: BLE001, the app's own crash ends the run
          self.crashes.append(crash_site(e, self.app))
          learn_from(e)
        rest = [t for t in asyncio.all_tasks() if t is not asyncio.current_task()
                and t not in older]
        if rest:
          await asyncio.wait(rest, timeout=DRAIN_SECONDS)
      try:
        if shared is not None:
          shared.run(main())
        else:
          asyncio.run(main())
      finally:
        out.put(done)
    with WorkRecorder(self.work) if CURRENT.files else contextlib.nullcontext():
      worker = threading.Thread(target=loop, name="lgauto-run", daemon=True)
      worker.start()
      deadline = time.monotonic() + RUN_SECONDS
      while True:
        try:
          ev = out.get(timeout=max(0.1, deadline - time.monotonic()))
        except queue.Empty:  # a hung run (a retry loop, a wait on a service) is abandoned
          frame = sys._current_frames().get(worker.ident)
          where = traceback.format_stack(frame)[-1].strip() if frame else "?"
          self.crashes.append(f"run timed out after {RUN_SECONDS:.0f}s at {where}"[:400])
          with tempfile.TemporaryFile("w+") as dump:
            faulthandler.dump_traceback(dump, all_threads=True)
            dump.seek(0)
            text = dump.read()
            if os.environ.get("LGAUTO_DUMP"):  # debugging aid, the full dump
              Path(os.environ["LGAUTO_DUMP"]).write_text(text)
            app_frames = [ln.strip() for ln in text.splitlines() if f"{self.app}" in ln]
          if os.environ.get("LGAUTO_DUMP"):
            with open(os.environ["LGAUTO_DUMP"], "a") as f:
              for task in list(asyncio.all_tasks(loops[0])) if loops else []:
                task.print_stack(limit=40, file=f)
          for task in list(asyncio.all_tasks(loops[0])) if loops else []:
            app_frames += [f"{f.f_code.co_filename}:{f.f_lineno}" for f in task.get_stack()
                           if str(self.app) in f.f_code.co_filename]
          self.crashes.append("hung in app frames: " + " | ".join(app_frames[:6])[:800])
          break
        if ev is done:
          break
        yield ev
      worker.join(timeout=1.0)
      drain(before)


class AppLoop:
  """One event loop in a thread for a whole worker, used with `--startup`. An app's startup
  makes connection pools and background tasks bound to the loop they were made on, so the
  probe and every run of the worker share that loop, as they do in the app's server."""

  def __init__(self) -> None:
    self.loop = asyncio.new_event_loop()
    self.stack = contextlib.AsyncExitStack()  # held, never closed: the worker exits hard
    self.thread = threading.Thread(target=self.loop.run_forever, name="lgauto-loop",
                                   daemon=True)
    self.thread.start()

  def run(self, coro: Any) -> Any:
    return asyncio.run_coroutine_threadsafe(coro, self.loop).result()


async def start_app(target: Any, stack: contextlib.AsyncExitStack) -> None:
  """Enter an app's startup and leave it open: the lifespan of a Starlette or FastAPI app, a
  lifespan or other context manager factory (each required argument, such as the app, gets
  None), or a plain or async function."""
  lifespan = getattr(getattr(target, "router", None), "lifespan_context", None)
  if lifespan is not None:
    await stack.enter_async_context(lifespan(target))
    return
  required = [p for p in inspect.signature(target).parameters.values()
              if p.default is p.empty
              and p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD)]
  out = target(*[None] * len(required))
  if hasattr(out, "__aenter__"):
    await stack.enter_async_context(out)
  elif hasattr(out, "__enter__"):
    stack.enter_context(out)
  elif inspect.isawaitable(out):
    await out


def drain(before: set[threading.Thread]) -> None:
  """Wait for the threads started during the run: timers and non-daemon threads up to
  `DRAIN_SECONDS`, other daemon threads up to `DAEMON_SECONDS`, idle pool workers not at all,
  since they never end on their own. A thread started from a daemon thread is a daemon too."""
  now = time.monotonic()
  deadline, daemon_deadline = now + DRAIN_SECONDS, now + DAEMON_SECONDS
  for t in [t for t in threading.enumerate() if t not in before
            and not re.search(r"ThreadPoolExecutor|asyncio|pool", t.name)]:
    long = isinstance(t, threading.Timer) or not t.daemon
    t.join(max(0.0, (deadline if long else daemon_deadline) - time.monotonic()))


class WorkRecorder(lgtrace.FileRecorder):
  """A `FileRecorder` that ignores code and bytecode, which the app imports, not reads."""

  def rel(self, path: Any) -> str | None:
    rel = super().rel(path)
    if rel is None or rel.endswith(CODE_SUFFIXES) or "__pycache__" in rel:
      return None
    return rel


# ---------------------------------------------------------------------------------------------
# Portable traces


def portable(value: Any, depth: int = 0) -> Any:
  """A picklable copy of a recorded value with the same string leaves."""
  if isinstance(value, str | int | float | bool | type(None)):
    return value
  if isinstance(value, bytes | bytearray):
    return bytes(value).decode(errors="replace")
  if depth > 30:
    return list(lgtrace.leaves(value))
  match value:
    case Mapping():
      return {str(k): portable(v, depth + 1) for k, v in value.items()}
    case list() | tuple() | set() | frozenset():
      return [portable(v, depth + 1) for v in value]
  if callable(getattr(value, "model_dump", None)) and not isinstance(value, type):
    with contextlib.suppress(Exception):
      return {"__type__": type(value).__name__, **portable(value.model_dump(), depth + 1)}
  if dataclasses.is_dataclass(value) and not isinstance(value, type):
    return {f.name: portable(getattr(value, f.name), depth + 1)
            for f in dataclasses.fields(value)}
  return list(lgtrace.leaves(value))


def portable_trace(trace: lgtrace.Trace) -> lgtrace.Trace:
  return dataclasses.replace(
    trace, inputs={k: portable(v) for k, v in trace.inputs.items()},
    accesses=tuple(dataclasses.replace(a, value=portable(a.value)) for a in trace.accesses))


# ---------------------------------------------------------------------------------------------
# Worker: one script in a fresh process


def compress_timers(cap: float = TIMER_CAP) -> None:
  """A `threading.Timer` fires after at most `cap` seconds, so debounced background work, such
  as a memory updater, runs before the run's drain gives up, and runs stay short."""
  init = threading.Timer.__init__

  def capped(self: threading.Timer, interval: float, *args: Any, **kwargs: Any) -> None:
    init(self, min(float(interval), cap), *args, **kwargs)
  threading.Timer.__init__ = capped  # type: ignore[method-assign]


WORK: list[Path] = []


def copy_app(repo: Path, work: Path) -> Path:
  app = work / "app"
  shutil.copytree(repo, app, symlinks=True,
                  ignore=shutil.ignore_patterns(".git", "node_modules", ".venv", "__pycache__"))
  return app


def prepare(req: Mapping[str, Any]) -> tuple[Path, Path, AppConfig]:
  """A fresh work dir with a copy of the repo, `HOME` and `TMPDIR` in it, the env set, every
  patch installed and the import roots on `sys.path`."""
  work = Path(tempfile.mkdtemp(prefix="lgauto-"))
  WORK.append(work)
  app = copy_app(Path(req["repo"]), work)
  for d in ("home", "tmp"):
    (work / d).mkdir()
  cfg = app_config(app) if not req.get("config") else AppConfig(**req["config"])
  for example, target in req.get("learned_files", []):
    if not (app / target).exists():
      shutil.copyfile(app / example, app / target)
  keys = {k: "lgauto-placeholder" for k in PLACEHOLDER_KEYS if not os.environ.get(k)}
  from_file = {k: v for k, v in config_env(app, cfg).items() if v}  # an empty value unsets
  learned = {k: "lgauto-placeholder" for k in req.get("learned_env", [])}
  env = {**OFFLINE_ENV, **keys, **learned, **from_file, **req.get("env", {})}
  os.environ.update({k: v.replace("{app}", str(app)) for k, v in env.items()})
  os.environ.update(HOME=str(work / "home"), TMPDIR=str(work / "tmp"))
  tempfile.tempdir = str(work / "tmp")
  os.chdir(app / cfg.base)
  block_network(req.get("services", []))
  seams = set(req.get("seams", SEAMS))
  lgseams.install_carriers()
  compress_timers()
  if "http" in seams:
    lgseams.install_http(req["markers"].values())
  for root in reversed(source_roots(app, cfg, req.get("paths", []))):
    add_path(root)
  install_models()
  install_tools()
  install_compile()
  if "db" in seams:
    lgseams.install_db()
  lgseams.install_memory(str(work), req["markers"].values()).enabled = "memory" in seams
  CURRENT.files = "file" in seams
  CURRENT.markers = dict(req["markers"])
  CURRENT.tools = req.get("tools", "guarded")
  return work, app, cfg


def worker(req: Mapping[str, Any]) -> dict[str, Any]:
  """Run one script of one graph and return its portable trace and what it met."""
  work, app, cfg = prepare(req)
  ref = GraphRef(**req["graph"])
  CURRENT.choices = dict(req.get("choices", {}))
  markers = CURRENT.markers
  if req.get("principal_setter"):
    mod, _, fn = req["principal_setter"].partition(":")
    CURRENT.setter = getattr(import_resolving(app, mod), fn)
  result: dict[str, Any] = {"used": {}, "crashes": [], "nodes": {}, "trace": None,
                            "error": None, "input": None, "stubbed": []}
  stage = "load"
  try:
    if req.get("startup"):  # `--startup`, setup for apps that initialise services first
      stage = "startup"
      mod, _, attr = req["startup"].partition(":")
      target = functools.reduce(getattr, attr.split("."), import_resolving(app, mod))
      CURRENT.loop = AppLoop()
      CURRENT.loop.run(start_app(target, CURRENT.loop.stack))
      stage = "load"
    obj = load_attr(app, cfg, ref)
  except BaseException as e:  # noqa: BLE001, the graph could not be loaded
    result["error"] = f"{stage}: {crash_site(e, app)}"
    learn_from(e)
    result.update(env_missing=sorted(set(CURRENT.env_missing)), missing=[],
                  files_missing=sorted(set(CURRENT.files_missing)))
    return result
  from langgraph.checkpoint.memory import InMemorySaver
  store = lgtrace.recording_store(make_store(cfg.store_index))
  entry = Entry(ref, obj, store, InMemorySaver(), app, work)
  try:
    probing = _probe(entry, run_config("A", "probe", ref.name))
    probe = CURRENT.loop.run(probing) if CURRENT.loop else asyncio.run(probing)
  except BaseException as e:  # noqa: BLE001
    result["error"] = f"build: {crash_site(e, app)}"
    learn_from(e)
    result.update(env_missing=sorted(set(CURRENT.env_missing)), missing=[],
                  files_missing=sorted(set(CURRENT.files_missing)))
    result["nodes"] = [sorted(g) for g in REGISTRY.graphs]
    return result
  schema = input_schema(probe)
  result["entry_nodes"] = sorted(static_nodes(probe)) if is_compiled(probe) else []
  runs = []
  for i, p in enumerate(req.get("order", ORDER)):
    thread = f"thread-{p}"
    runs.append(lgtrace.Run(fill_input(schema, p, markers[p], req.get("input_keys", [])), p,
                            run_config(p, thread, ref.name)))
  result["input"] = portable(runs[0].input)
  trace = lgtrace.Trace(dict(markers))
  for j, run in enumerate(runs):
    CURRENT.principal = run.principal or ""
    trace = trace + lgtrace.run_trace(entry, run, store, markers, f"{req['index']}.{j}", None,
                                      lgtrace.thread_of(run, j))
  result.update(trace=portable_trace(trace), used=dict(CURRENT.used), crashes=entry.crashes,
                nodes=[sorted(g) for g in REGISTRY.graphs],
                stubbed=sorted(set(CURRENT.stubbed)), missing=sorted(set(CURRENT.missing)),
                stubbed_modules=sorted(set(STUBBED_MODULES)),
                env_missing=sorted(set(CURRENT.env_missing)),
                files_missing=sorted(set(CURRENT.files_missing)))
  return result


async def _probe(entry: Entry, config: Mapping[str, Any]) -> Any:
  """A graph built once before the runs, outside any run, to read its input schema."""
  if is_compiled(entry.obj):
    return entry.obj
  if is_builder(entry.obj):
    return entry.obj.compile()
  out = await call_factory(entry.obj, config)
  return out.compile() if is_builder(out) else out


def make_store(index: Mapping[str, Any] | None) -> Any:
  from langgraph.store.memory import InMemoryStore
  if not index:
    return InMemoryStore()
  from langchain_core.embeddings import DeterministicFakeEmbedding
  dims = int(index.get("dims", EMBED_DIMS))
  fields = index.get("fields")
  conf: dict[str, Any] = {"dims": dims, "embed": DeterministicFakeEmbedding(size=dims)}
  if fields:
    conf["fields"] = fields
  return InMemoryStore(index=conf)


def worker_main(req_path: str, out_path: str) -> None:
  req = json.loads(Path(req_path).read_text())
  try:
    result = worker(req)
  except BaseException as e:  # noqa: BLE001, report rather than die
    result = {"error": f"worker: {type(e).__name__}: {e}", "used": dict(CURRENT.used),
              "crashes": [], "nodes": {}, "trace": None, "input": None, "stubbed": [],
              "traceback": traceback.format_exc()[-3000:]}
  with open(out_path, "wb") as f:
    pickle.dump(result, f)
  sys.stdout.flush()
  for work in WORK:
    shutil.rmtree(work, ignore_errors=True)
  os._exit(0)  # leftover app threads must not keep the worker alive


# ---------------------------------------------------------------------------------------------
# Driver


@dataclass
class Options:
  repo: Path
  graphs: tuple[str, ...] = ()
  env: Mapping[str, str] = field(default_factory=dict)
  paths: tuple[str, ...] = ()
  tools: str = "guarded"
  max_scripts: int = MAX_SCRIPTS
  out: Path | None = None
  name: str = ""
  attackers: tuple[str, ...] = ATTACKERS
  python: str = sys.executable
  write: bool = True
  seams: tuple[str, ...] = SEAMS
  principal_setter: str = ""
  services: tuple[str, ...] = ()
  startup: str = ""

  @property
  def setup(self) -> list[str]:
    """Every flag beyond the repo, which counts as per-app setup."""
    return ([f"--graph {g}" for g in self.graphs] + [f"--env {k}={v}" for k, v in self.env.items()]
            + [f"--path {p}" for p in self.paths] + (["--tools stub"] if self.tools == "stub"
                                                      else [])
            + ([f"--principal-setter {self.principal_setter}"] if self.principal_setter else [])
            + [f"--service {s}" for s in self.services]
            + ([f"--startup {self.startup}"] if self.startup else []))
    # `--seams`, `--max-scripts`, `--attacker` and `--name` are ablations and reporting, not setup


def run_worker(opts: Options, cfg: AppConfig, ref: GraphRef, markers: Mapping[str, str],
               index: int, choices: Mapping[str, int], keys: Sequence[str] = (),
               learned_env: Sequence[str] = (),
               learned_files: Sequence[tuple[str, str]] = ()) -> dict[str, Any]:
  with tempfile.TemporaryDirectory(prefix="lgauto-req-") as tmp:
    req = {"repo": str(opts.repo), "graph": dataclasses.asdict(ref),
           "config": dataclasses.asdict(cfg), "env": dict(opts.env), "paths": list(opts.paths),
           "markers": dict(markers), "choices": dict(choices), "tools": opts.tools,
           "order": list(ORDER), "index": index, "seams": list(opts.seams),
           "input_keys": list(keys), "learned_env": list(learned_env),
           "principal_setter": opts.principal_setter, "services": list(opts.services),
           "startup": opts.startup,
           "learned_files": [list(f) for f in learned_files]}
    req_path, out_path = Path(tmp) / "req.json", Path(tmp) / "out.pkl"
    req_path.write_text(json.dumps(req))
    try:
      proc = subprocess.run([opts.python, "-m", "lgauto", "--worker", str(req_path),
                             str(out_path)], cwd=PY_DIR, capture_output=True, text=True,
                            timeout=WORKER_TIMEOUT)
    except subprocess.TimeoutExpired:
      return {"error": f"worker timed out after {WORKER_TIMEOUT}s", "used": {}, "crashes": [],
              "nodes": {}, "trace": None, "input": None, "stubbed": []}
    if not out_path.exists():
      return {"error": f"worker died ({proc.returncode}): {proc.stderr[-1500:]}", "used": {},
              "crashes": [], "nodes": {}, "trace": None, "input": None, "stubbed": []}
    with open(out_path, "rb") as f:
      return pickle.load(f)


def analyse(name: str, ref: GraphRef, opts: Options, markers: Mapping[str, str],
            kept: Sequence[tuple[dict[str, int], dict[str, Any], dict[str, list[str]]]]
            ) -> dict[str, Any]:
  """Merge the scripts' traces and turn them into the spec, findings and coverage."""
  results = [r for _, r, _ in kept]
  traces = [r["trace"] for r in results if r.get("trace") is not None]
  errors = sorted({r["error"] for r in results if r.get("error")})
  crashes = [c for r in results for c in r.get("crashes", [])]
  graphs = {frozenset(g) for r in results for g in r.get("nodes", [])}
  entry = {n for r in results for n in r.get("entry_nodes", [])}
  summary: dict[str, Any] = {
    "name": name, "graph": ref.name, "setup": opts.setup, "scripts": len(kept),
    "decisions": sorted({k for _, _, u in kept for k in u}), "errors": errors,
    "crashes": {c: crashes.count(c) for c in sorted(set(crashes))},
    "stubbed_tools": sorted({s.split(":")[0] for r in results for s in r.get("stubbed", [])}),
    "input": next((r["input"] for r in results if r.get("input") is not None), None),
    "stubbed_modules": sorted({m for r in results for m in r.get("stubbed_modules", [])}),
  }
  if not traces:
    return {**summary, "ran": False, "findings": {}, "unexplained": [], "spec": None,
            "nodes_total": sorted(entry), "nodes_ran": []}
  trace = functools.reduce(lgtrace.Trace.__add__, traces)
  attackers = frozenset(opts.attackers)
  data = lgtrace.spec_dict(trace, attackers)
  spec = irspec.from_dict(data)
  executed = {a.node.rsplit("/", 1)[-1] for a in trace.accesses}
  # the entry graph and its static subgraphs, plus every graph some node of which ran, such
  # as a subgraph a node invokes or a graph a factory builds per run
  # (a graph counts only when a node it does not share with the entry graph ran, since
  # common names such as `model` and `tools` recur across an app's graphs)
  total = entry.union(*(g for g in graphs if (g - entry) & executed))
  ran = executed & total
  other = frozenset(PRINCIPALS) - attackers
  reverse = lgtrace.findings(lgtrace.to_spec(trace, other)) if other else {}
  out_path = None
  if opts.write:
    out_dir = opts.out or PY_DIR.parent / "specs" / "auto"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{name}.json"
    out_path.write_text(json.dumps(data, indent=2) + "\n")
  return {**summary, "ran": True,
          "findings": lgtrace.findings(spec),
          "findings_reverse": sorted(reverse),
          "flows": sorted(map(list, lgtrace.flows(trace))),
          "unexplained": sorted(map(list, lgtrace.unexplained(trace, attackers))),
          "cross_reads": len(lgtrace.cross_reads(trace)),
          "fallbacks": sorted(trace.fallbacks), "unattributed": trace.unattributed,
          "nodes_total": sorted(total), "nodes_ran": sorted(ran),
          "spec": str(out_path) if out_path else None}


def learn(opts: Options, cfg: AppConfig, ref: GraphRef, markers: Mapping[str, str],
          counter: Iterator[int], rounds: int = 12
          ) -> tuple[list[str], list[str], list[tuple[str, str]]]:
  """Input keys an untyped input dict needs and environment variables the app requires, learnt
  from the crashes of default runs (`learn_from`). Each round adds what the last run missed,
  input keys to every free-form dict of the input and variables as placeholders, until
  nothing is new."""
  keys: list[str] = []
  env: list[str] = []
  files: list[tuple[str, str]] = []
  for _ in range(rounds):
    r = run_worker(opts, cfg, ref, markers, next(counter), {}, keys, env, files)
    new_keys = [k for k in r.get("missing", []) if k not in keys]
    new_env = [k for k in r.get("env_missing", []) if k not in env and k not in opts.env]
    found = [example_for(opts.repo, n) for n in r.get("files_missing", [])]
    new_files = [f for f in dict.fromkeys(found) if f and f not in files]
    if not (new_keys or new_env or new_files):
      break
    keys += new_keys
    env += new_env
    files += new_files
  return keys, env, files


def check(opts: Options) -> list[dict[str, Any]]:
  """Every selected graph of the repo, explored and analysed."""
  cfg = app_config(opts.repo)
  refs = select(cfg.graphs, opts.graphs)
  markers = lgtrace.make_markers(PRINCIPALS)
  base = opts.name or opts.repo.name
  summaries = []
  for ref in refs:
    counter = iter(range(10**6))
    keys, env, files = learn(opts, cfg, ref, markers, counter)

    def one(choices: dict[str, int], ref: GraphRef = ref) -> tuple[Any, Mapping[str, Any]]:
      r = run_worker(opts, cfg, ref, markers, next(counter), choices, keys, env, files)
      return r, r.get("used", {})
    kept = explore(one, opts.max_scripts)
    label = ref.name if len(refs) > 1 or not opts.name else ""
    name = "-".join(x for x in (base, re.sub(r"[^\w.-]+", "_", label)) if x)
    summaries.append({**analyse(name, ref, opts, markers, kept), "input_keys": keys,
                      "learned_env": env, "learned_files": files})
  return summaries


def print_summary(s: Mapping[str, Any]) -> None:
  print(f"== {s['name']} ({s['graph']}): ran {s['ran']}, {s['scripts']} scripts, "
        f"{len(s['findings'])} findings, {len(s['unexplained'])} unexplained, nodes "
        f"{len(s['nodes_ran'])}/{len(s['nodes_total'])}, spec {s['spec']}")
  print(f"setup: {' '.join(s['setup']) or 'none'}")
  for e in s["errors"]:
    print(f"error {e}")
  for victim, path in s["findings"].items():
    print(f"finding {victim}")
    print("".join(f"  {step}\n" for step in path), end="")
  for src, channel, reader in s["unexplained"]:
    print(f"unexplained flow {src} -> {channel} -> {reader}")
  for c, n in s["crashes"].items():
    print(f"app crash in {n} runs: {c}")
  if s.get("stubbed_modules"):
    print(f"stubbed modules (not installed): {', '.join(s['stubbed_modules'])}")
  if s.get("stubbed_tools"):
    print(f"stubbed tools: {', '.join(s['stubbed_tools'])}")
  if s.get("fallbacks"):
    print(f"reads not tracked, whole input used: {', '.join(s['fallbacks'])}")


def parse(argv: Sequence[str] | None = None) -> Options:
  ap = argparse.ArgumentParser(prog="lgauto", description=__doc__.split("\n", 1)[0])
  ap.add_argument("repo", type=Path)
  ap.add_argument("--graph", action="append", default=[], help="graph name or attr")
  ap.add_argument("--env", action="append", default=[], metavar="KEY=VAL",
                  help="`{app}` is the repo copy")
  ap.add_argument("--path", action="append", default=[], help="extra import root in the repo")
  ap.add_argument("--tools", choices=("guarded", "stub"), default="guarded")
  ap.add_argument("--max-scripts", type=int, default=MAX_SCRIPTS)
  ap.add_argument("--out", type=Path)
  ap.add_argument("--name", default="")
  ap.add_argument("--attacker", action="append", default=[])
  ap.add_argument("--no-write", action="store_true")
  ap.add_argument("--principal-setter", default="", metavar="MODULE:FN",
                  help="called with the run's user before each run, for apps that take the "
                       "user from somewhere other than the run config")
  ap.add_argument("--service", action="append", default=[], metavar="HOST:PORT",
                  help="a service the app's clients may connect to, such as its database")
  ap.add_argument("--startup", default="", metavar="MODULE:ATTR",
                  help="the app's startup (an ASGI app, a lifespan or a function), entered once "
                       "per worker before the graph loads")
  ap.add_argument("--seams", default=",".join(SEAMS), help="ablation, a subset of " + ",".join(SEAMS))
  args = ap.parse_args(argv)
  return Options(args.repo.resolve(), tuple(args.graph),
                 dict(e.split("=", 1) for e in args.env), tuple(args.path), args.tools,
                 args.max_scripts, args.out, args.name,
                 tuple(args.attacker) or ATTACKERS, sys.executable, not args.no_write,
                 tuple(x for x in args.seams.split(",") if x), args.principal_setter,
                 tuple(args.service), args.startup)


def main(argv: Sequence[str] | None = None) -> None:
  argv = list(sys.argv[1:] if argv is None else argv)
  if argv[:1] == ["--worker"]:
    worker_main(argv[1], argv[2])
    return
  summaries = check(parse(argv))
  for s in summaries:
    print_summary(s)
  print("LGAUTO_JSON " + json.dumps(summaries, default=str))


if __name__ == "__main__":
  main()
