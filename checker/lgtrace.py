"""Dynamic extractor from a LangGraph run to an `irspec` spec.

One concrete run with a marker-copying fake LLM stands in for every run, as in Lancet. Each
principal's input carries a unique marker string, the fake LLM copies every marker it sees into
its output, and the extractor watches where the markers travel.

Layers
- Core, free of LangGraph. `Trace` holds pure data (`Access` records), and `trace_from_events`
  builds one from raw debug events, store operations and tracked reads. `spec_dict`, `to_spec`
  and `findings` turn a trace into an `irspec` spec and its findings.
- Hooks, importing LangGraph lazily. `instrument` wraps a `StateGraph` so each node records the
  state keys it accesses, `instrument_compiled` does so for a compiled graph such as one from
  `create_agent`, `RecordingStore` wraps a `BaseStore`, `marker_llm` builds the fake LLM,
  `run_trace` streams one compiled graph, and `trace_subject`/`extract` drive a whole subject
  over every router script.
- Resource recorders, free of LangGraph (next section).

Reads
- A task reads a state key only if its code accesses it. `instrument(builder)` returns a copy of
  a `StateGraph` whose node runnables and conditional-edge functions get the state through a
  tracking proxy, a `dict` subclass for dict states and an attribute proxy for pydantic and
  dataclass states. Each access logs the key, a copy of the value and the task id from the
  `checkpoint_ns` of the config LangGraph passes in. A routing function counts as part of the
  task of its source node. LangGraph has no hook that reports key accesses, so the copy swaps
  `runnable` in the public `builder.nodes` specs and `path` in `builder.branches`, and leaves
  LangGraph's internals alone. A node that is a compiled subgraph is recompiled from its own
  instrumented builder with the same compile settings.
- Returning the state object unchanged (`return state`) is a pass-through, not a read, since it
  writes each key's own value back to that key.
- A task that wraps a subgraph only contains the subgraph's tasks, so it has no reads of its own.
- A task whose input could not be tracked, such as a node of an uninstrumented graph or a node
  whose input is not a state mapping or object, falls back to its whole debug-event input as
  read. `Trace.fallbacks` lists those tasks and `trace_subject` warns about them.

Spec rules
- Agents are `node@P` for every observed task and `input@P` for every principal `P`. A node
  inside a subgraph is named by its path, as in `outer/inner`.
- Channels are state keys (`msgs`), store namespaces (`store:a/b`) and resources outside
  LangGraph (`file:memory.json`). State keys live per thread, so the channel `K` for `P` in
  thread `T` is `K#P/T`. A run's thread is its `configurable.thread_id`, or `run<j>` for the
  j-th run of a script without one. Store namespaces and resources are shared across threads,
  so theirs is `K#P`.
- Boards are directional and split by writer. A task that reads `K` and sees `P`'s marker in a
  string `s` reads board `K#P/T<-w` for every task `w` that wrote `s` to `K` earlier in the same
  script and thread, and `w` writes that board. Flow goes from writers to readers only. Without
  the split, `K#P/T` would link every writer of `P`'s marker to every reader at any time, so a
  later task rewriting old text (kaymen99's `email_proofreader@B` rewriting A's drafts) would
  reach earlier readers of it.
- A reader whose string no recorded write to `K` contains, such as text a node appended to a
  channel value in place, reads the whole board `K#P/T`. Its writers are the tasks that wrote a
  value carrying `P`'s marker to `K`, and the tasks serving `P` that wrote `K` at all.
- Board `in#P` has writer `input@P` and, as readers, the tasks of `P` that read raw input text
  of `P`. Raw input means a string leaf that occurs verbatim in the same run's input.
- Raw input text is credited to the input it came from, not to the tasks that wrote it on. In
  kaymen99 `skip_unrelated_email@A` returns the state with B's email in it, and crediting that
  write would make `categorize_email@B`, reading its own email, reached from A.
- Raw input text of another principal carries no flow. Read tracking does not make this rule
  redundant, since it works per key. In kaymen99 every task of the first customer reads the
  whole inbox key or a routing function does (`check_new_emails`, `must_rewrite`), so without
  the rule, with the second customer as attacker, seven tasks of the first customer would be
  findings. Runs serving one principal each never see another principal's raw text.
- The adversary controls `input@A` for each attacker `A`. A finding is a reached `node@B` with
  `B` not an attacker, together with its `irspec.explain` path.
- `Rules` switches each of the last three rules off, for the tests that show they are needed.

Resources outside LangGraph
- Apps keep shared state that LangGraph never sees, such as memory files, in-process caches and
  work queues. Recorders turn each access into the same kind of op as a store op, on a channel
  `scheme:name` (`file:memory.json`, `ext:memory`, `queue:memory`). Such channels are shared
  across threads, like store namespaces, so their boards are `K#P` with no thread.
- `FileRecorder(root)` records opens, renames and removals under `root` through CPython's
  audit hooks, the narrowest seam that every file API passes. `recorded(fn, mode, channel)`
  wraps a method of an app's own storage class, which is the seam to use when the app caches
  above its files, since a cached load opens nothing. `emit` records one access by hand.
- An access belongs to `current_task()`, an open external task first, else the LangGraph task
  from `get_config`. `acting(node)` opens an external task, such as a graph factory or a
  background updater, which acts for its parent task's principal or the run's. A context
  variable does not cross into a `threading.Thread`, a `threading.Timer` or a
  `ThreadPoolExecutor`, so `Handoff` carries the attribution across a queue explicitly. An
  external task whose parent the run does not know counts as unattributed.
- A graph factory bakes values into the graph it returns, such as a system prompt read from a
  memory file. It writes them to a `built:` channel, and `built_reads` makes each fake-LLM call
  whose input contains a marker-carrying line of the value a read of it by the calling task.
- `unexplained(trace, attackers)` lists flows whose reader the spec does not reach. The marker
  shows the attacker's text arrived, so each one is a path some recorder missed.

Reports beside the findings
- `flows(trace)` lists the concrete cross-principal marker reads, as (source, channel, reader).
- `cross_reads(trace)` lists reads that markers cannot see. A task serving `B` reads a key or
  namespace whose last write before it, in the same script and thread, came from a task
  serving another principal `A`, and the value read carries no marker of `A`. An integer such
  as a retry counter left behind by `A` shows up here. So does every benign reset, since the
  read cannot tell a value that depends on `A` from a constant `A` happened to write.

What an adapter supplies, as a `Subject`
- `build(store, script)`, which returns the compiled graph. It must compile `instrument(g)`
  with the given `store` (a `RecordingStore`) and wire in `marker_llm(markers, script)` and
  tool stubs. A graph compiled without `instrument` still traces, with every task falling back.
- `runs`, each a `Run(input, principal, config, resumes)`. Runs of one script share the store
  and graph, in order. `principal` labels a run that serves one principal. `resumes` are fed
  back as `Command(resume=r)` after interrupts, which needs a checkpointer and a `thread_id`.
- `markers`, mapping each principal to its marker, as made by `make_markers`. The adapter puts
  each marker into that principal's input text.
- `attackers`, the principals whose input the adversary writes.
- `scripts`, one fake-LLM script per router outcome to explore, as made by `router_scripts`.
- `principal_of(node, task_input)`, optional, for runs that batch several principals. It returns
  a principal or None, and None falls back to the parent task, then to the run label, then `*`.
  It sees the task's whole input from the debug event, whatever the task reads.
- `store`, an optional factory for the base store, an `InMemoryStore` by default.

What it gets back
- `trace_subject(subject)` gives the merged `Trace`. `extract(subject)` gives the `irspec.Spec`,
  `spec_dict(trace, attackers)` its JSON form, and `findings(spec)` maps each reached victim
  task to its flow path.

Fake LLM scripts
- A script maps a key to a response or to a callable from the call index to a response, and
  `seq(r0, r1, ...)` makes one that repeats its last item. The key `text` scripts plain replies
  and `tool_calls` scripts lists of `{"name", "args"}` tool calls. A structured-output schema is
  scripted under its class name by a dict of field values. Unscripted `str` fields get the
  copied markers. Every scripted string has `{markers}` replaced by the markers seen.

Example
    markers = make_markers(["A", "B"])
    subject = Subject(
      build=lambda store, script: instrument(make_graph(marker_llm(markers, script)))
        .compile(store=store),
      runs=(Run({"email": f"hi {markers['A']}"}, "A"), Run({"email": f"yo {markers['B']}"}, "B")),
      markers=markers, attackers=frozenset({"A"}),
      scripts=router_scripts({"Router": [{"route": "ignore"}, {"route": "respond"}]}))
    print(findings(extract(subject)))
"""

from __future__ import annotations

import contextlib
import contextvars
import copy
import dataclasses
import functools
import inspect
import itertools
import json
import os
import sys
import threading
import uuid
import warnings
from collections import defaultdict
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Literal

import irspec

Mode = Literal["read", "write"]
Role = Literal["reader", "writer"]
SHARED = "*"
STORE_PREFIX = "store:"
FILE_PREFIX = "file:"
BUILT_PREFIX = "built:"


# ---------------------------------------------------------------------------------------------
# Core data


@dataclass(frozen=True)
class Access:
  """One task reading or writing one channel value.

  `thread` names the run's thread, which scopes state keys. `seq` orders accesses in time.
  """
  run: str
  task: str
  node: str
  principal: str
  channel: str
  mode: Mode
  value: Any
  thread: str = ""
  seq: int = 0

  @property
  def agent(self) -> str:
    return agent_name(self.node, self.principal)

  @property
  def is_store(self) -> bool:
    return is_shared(self.channel)

  @property
  def scope(self) -> tuple[str, str]:
    """Where the channel's value lives, the script and, for a state key, the thread."""
    return script_of(self.run), "" if self.is_store else self.thread


@dataclass(frozen=True)
class StoreOp:
  """One store or resource access as its recorder saw it, before task attribution.

  A store op names its namespace, and a resource op (a file, a queue, an app's own storage)
  names its `channel` directly, such as `file:memory.json`.
  """
  task: str | None
  namespace: tuple[str, ...]
  mode: Mode
  value: Any
  seq: int = 0
  channel: str = ""

  @property
  def where(self) -> str:
    return self.channel or store_channel(self.namespace)


@dataclass(frozen=True)
class ExternalTask:
  """A task that ran outside LangGraph's scheduler, such as a background updater or a graph
  factory. It acts for `principal`, or when that is None for its `parent` task, or else for the
  run's principal. A parent that the run does not know leaves the task unattributed."""
  task: str
  node: str
  principal: str | None = None
  parent: str | None = None
  seq: int = 0


@dataclass(frozen=True)
class LLMCall:
  """One call of the fake LLM, with the task it ran in and a copy of its input."""
  task: str | None
  value: Any
  seq: int = 0


@dataclass(frozen=True)
class ReadOp:
  """One state-key access by tracked node code, before task attribution.

  `route` marks an access by a routing function, which runs after its node's writes.
  """
  task: str | None
  key: str
  value: Any
  seq: int = 0
  route: bool = False


@dataclass(frozen=True)
class Stamped:
  """A debug event with the time it was received, on the clock of `ReadOp` and `StoreOp`."""
  seq: int
  event: Any


@dataclass(frozen=True)
class Graph:
  """One instrumented `StateGraph`, its node names and the kind of each state key's channel,
  such as `LastValue` or `BinaryOperatorAggregate`."""
  nodes: frozenset[str]
  channels: Mapping[str, str]

  def key(self) -> tuple[frozenset[str], tuple[tuple[str, str], ...]]:
    return self.nodes, tuple(sorted(self.channels.items()))


@dataclass(frozen=True)
class Trace:
  """Accesses of one or more runs. `fallbacks` names the tasks whose reads were not tracked, and
  `relays` holds the (run, task id) of tasks that returned their state unchanged.

  The ordered analysis (`ordered_dict`) also uses
  - `tracked`, the (run, task id) of tasks whose node code ran under a read proxy,
  - `containers`, the (run, task id) of tasks that contain a subgraph's tasks,
  - `llm_tasks`, the (run, task id, node) of tasks that called the fake LLM, and `llm_lost`,
    the runs with a call no task could be found for,
  - `passes`, the (run, task id, key) of writes whose value is the very object the state held
    for that key when the node was called, unchanged since,
  - `graphs`, every instrumented graph,
  - `steps` and `parents`, each graph task's superstep and the task id of the subgraph task it
    runs in, and `spans`, each task's first and last live time (see `trace_from_events`).
  """
  markers: Mapping[str, str]
  inputs: Mapping[str, Any] = field(default_factory=dict)
  accesses: tuple[Access, ...] = ()
  unattributed: int = 0
  fallbacks: frozenset[str] = frozenset()
  relays: frozenset[tuple[str, str]] = frozenset()
  tracked: frozenset[tuple[str, str]] = frozenset()
  containers: frozenset[tuple[str, str]] = frozenset()
  llm_tasks: frozenset[tuple[str, str, str]] = frozenset()
  llm_lost: frozenset[str] = frozenset()
  passes: frozenset[tuple[str, str, str]] = frozenset()
  graphs: tuple[Graph, ...] = ()
  steps: Mapping[tuple[str, str], int] = field(default_factory=dict)
  parents: Mapping[tuple[str, str], str] = field(default_factory=dict)
  spans: Mapping[tuple[str, str], tuple[int, int]] = field(default_factory=dict)

  def __add__(self, other: Trace) -> Trace:
    if dict(self.markers) != dict(other.markers):
      raise ValueError("cannot merge traces with different markers")
    graphs = {g.key(): g for g in (*self.graphs, *other.graphs)}
    return Trace(self.markers, {**self.inputs, **other.inputs},
                 self.accesses + other.accesses, self.unattributed + other.unattributed,
                 self.fallbacks | other.fallbacks, self.relays | other.relays,
                 self.tracked | other.tracked, self.containers | other.containers,
                 self.llm_tasks | other.llm_tasks, self.llm_lost | other.llm_lost,
                 self.passes | other.passes, tuple(graphs.values()),
                 {**self.steps, **other.steps}, {**self.parents, **other.parents},
                 {**self.spans, **other.spans})


def agent_name(node: str, principal: str) -> str:
  return f"{node}@{principal}"


def principal_part(agent: str) -> str:
  return agent.rpartition("@")[2]


def store_channel(namespace: Iterable[str]) -> str:
  return STORE_PREFIX + "/".join(namespace)


def script_of(run: str) -> str:
  """The script of run id `i.j`, whose runs share a store, graph and checkpointer."""
  return run.partition(".")[0]


def is_shared(channel: str) -> bool:
  """Whether a channel lives outside a thread's state. State keys never contain `:`, while store
  namespaces and resources are `scheme:name`."""
  return ":" in channel


def board_name(channel: str, principal: str, thread: str = "") -> str:
  """`K#P` for a store namespace, resource or threadless key, `K#P/T` for a state key in `T`."""
  base = f"{channel}#{principal}"
  return base if is_shared(channel) or not thread else f"{base}/{thread}"


def make_markers(principals: Iterable[str]) -> dict[str, str]:
  """A unique marker per principal, distinct enough that no marker contains another."""
  return {p: f"MK{uuid.uuid4().hex[:8]}x{i}Z" for i, p in enumerate(principals)}


# ---------------------------------------------------------------------------------------------
# Marker detection


def leaves(value: Any, _seen: frozenset[int] = frozenset()) -> Iterator[str]:
  """Every string inside `value`, through containers, pydantic models, dataclasses and slots."""
  if isinstance(value, str):
    yield value
    return
  if isinstance(value, bytes | bytearray):
    yield bytes(value).decode(errors="replace")
    return
  if value is None or isinstance(value, int | float | bool) or id(value) in _seen:
    return
  seen = _seen | {id(value)}
  match value:
    case Mapping():
      children: Iterable[Any] = itertools.chain.from_iterable(value.items())
    case list() | tuple() | set() | frozenset():
      children = value
    case _ if callable(getattr(value, "model_dump", None)) and not isinstance(value, type):
      children = [value.model_dump()]
    case _ if dataclasses.is_dataclass(value) and not isinstance(value, type):
      children = [getattr(value, f.name) for f in dataclasses.fields(value)]
    case _:
      slots = [s for c in type(value).__mro__ for s in getattr(c, "__slots__", ())]
      children = [*getattr(value, "__dict__", {}).values(),
                  *(getattr(value, s) for s in slots if hasattr(value, s))]
  for child in children:
    yield from leaves(child, seen)


def owners(texts: Iterable[str], markers: Mapping[str, str]) -> frozenset[str]:
  ts = tuple(texts)
  return frozenset(p for p, m in markers.items() if any(m in t for t in ts))


def split_markers(value: Any, raw: frozenset[str],
                  markers: Mapping[str, str]) -> tuple[frozenset[str], frozenset[str]]:
  """Principals whose marker `value` carries in raw input leaves, and in all other leaves."""
  ls = [t for t in leaves(value) if any(m in t for m in markers.values())]
  return owners((t for t in ls if t in raw), markers), owners((t for t in ls if t not in raw),
                                                             markers)


# ---------------------------------------------------------------------------------------------
# Trace to spec


def _raw_leaves(trace: Trace) -> dict[str, frozenset[str]]:
  return {run: frozenset(t for t in leaves(inp) if owners([t], trace.markers))
          for run, inp in trace.inputs.items()}


@dataclass(frozen=True)
class Rules:
  """Switches for the spec rules, all on by default. Tests turn one off to show it is needed.

  - `raw_rule`, another principal's raw input text carries no flow. Off, a task reading it
    reads that principal's `in#Q`.
  - `raw_from_input`, raw input text is credited to the input it came from. Off, it is
    credited to the tasks that wrote it to the channel, like any other text.
  - `split`, one board per channel, principal, thread and writer. Off, one board per channel,
    principal and thread.
  """
  raw_rule: bool = True
  raw_from_input: bool = True
  split: bool = True


@dataclass(frozen=True)
class _Classified:
  access: Access
  raw: frozenset[str]
  flow: frozenset[str]
  marked: frozenset[str]


def _classify(trace: Trace, rules: Rules) -> list[_Classified]:
  raw = _raw_leaves(trace) if rules.raw_from_input else {}
  def one(a: Access) -> _Classified:
    run_raw = raw.get(a.run, frozenset())
    marked = frozenset(t for t in leaves(a.value)
                       if t not in run_raw and owners([t], trace.markers))
    return _Classified(a, *split_markers(a.value, run_raw, trace.markers), marked)
  return [one(a) for a in trace.accesses]


def split_board(board: str, writer: str) -> str:
  """The part of `board` that holds what `writer` wrote."""
  return f"{board}<-{writer}"


def roles(trace: Trace, rules: Rules = Rules()) -> Iterator[tuple[str, Role, str]]:
  """(board, role, agent) triples under the spec rules in the module docstring."""
  return ((board, role, agent) for board, role, agent, _ in located_roles(trace, rules))


INPUT_CHANNEL = ""


def located_roles(trace: Trace, rules: Rules = Rules()
                  ) -> Iterator[tuple[str, Role, str, tuple[str, str]]]:
  """`roles` with the (channel, thread) of the access behind each one. A read of `in#P` is
  located at the channel the raw text was read from, and the writes of `in#P` at
  `INPUT_CHANNEL`."""
  yield from ((f"in#{p}", "writer", agent_name("input", p), (INPUT_CHANNEL, ""))
              for p in trace.markers)
  cs = _classify(trace, rules)
  writes: defaultdict[tuple[str, str, str], list[_Classified]] = defaultdict(list)
  coarse: defaultdict[str, set[str]] = defaultdict(set)
  where: dict[str, tuple[str, str]] = {}
  for c in cs:
    a = c.access
    if a.mode == "write":
      writes[(*a.scope, a.channel)].append(c)
      for p in c.flow | frozenset({a.principal} - {SHARED}):
        board = board_name(a.channel, p, a.thread)
        coarse[board].add(a.agent)
        where[board] = (a.channel, a.thread)
  needed: set[str] = set() if rules.split else set(coarse)
  for c in (c for c in cs if c.access.mode == "read"):
    a = c.access
    at = (a.channel, a.thread)
    from_input = c.raw if not rules.raw_rule else c.raw & {a.principal}
    yield from ((f"in#{p}", "reader", a.agent, at) for p in sorted(from_input))
    if not rules.raw_from_input and a.principal in c.flow:
      yield f"in#{a.principal}", "reader", a.agent, at
    for p in sorted(c.flow):
      board = board_name(a.channel, p, a.thread)
      seen = frozenset(t for t in c.marked if trace.markers[p] in t)
      sources = sorted({w.access.agent for w in writes[(*a.scope, a.channel)]
                        if w.access.seq <= a.seq and seen & w.marked} if rules.split else ())
      for w in sources:
        yield split_board(board, w), "writer", w, at
        yield split_board(board, w), "reader", a.agent, at
      if not sources:
        needed.add(board)
        yield board, "reader", a.agent, at
  yield from ((b, "writer", w, where[b]) for b in sorted(needed) for w in sorted(coarse[b]))


def spec_dict(trace: Trace, attackers: Iterable[str], rules: Rules = Rules()) -> dict[str, Any]:
  """The trace as `irspec` JSON with `{"readers", "writers"}` boards."""
  attackers = frozenset(attackers)
  if unknown := attackers - set(trace.markers):
    raise ValueError(f"attackers without markers: {sorted(unknown)}")
  boards: defaultdict[str, dict[Role, set[str]]] = defaultdict(
    lambda: {"reader": set(), "writer": set()})
  for board, role, agent in roles(trace, rules):
    boards[board][role].add(agent)
  agents = sorted({*(agent_name("input", p) for p in trace.markers),
                   *(a.agent for a in trace.accesses)})
  return {
    "agents": agents,
    "boards": {b: {"readers": sorted(r["reader"]), "writers": sorted(r["writer"])}
               for b, r in sorted(boards.items())},
    "owner": {},
    "sees": "none",
    "echo_sees": "none",
    "adversary": {"controls": sorted(agent_name("input", p) for p in attackers)},
  }


def to_spec(trace: Trace, attackers: Iterable[str], rules: Rules = Rules()) -> irspec.Spec:
  return irspec.from_dict(spec_dict(trace, attackers, rules))


def attackers_of(spec: irspec.Spec) -> frozenset[str]:
  return frozenset(principal_part(a) for a in spec.controls)


def findings(spec: irspec.Spec) -> dict[str, list[str]]:
  """Reached tasks of non-attacker principals, each with a shortest flow path."""
  bad = attackers_of(spec)
  return {a: path for a, path in sorted(irspec.explain(spec).items())
          if not a.startswith("input@") and principal_part(a) not in bad}


def flows(trace: Trace) -> frozenset[tuple[str, str, str]]:
  """Concrete (source principal, channel, reading agent) marker reads across principals."""
  raw = _raw_leaves(trace)
  return frozenset(
    (p, a.channel, a.agent)
    for a in trace.accesses if a.mode == "read"
    for p in split_markers(a.value, raw.get(a.run, frozenset()), trace.markers)[1]
    if p != a.principal)


def unexplained(trace: Trace, attackers: Iterable[str],
                rules: Rules = Rules()) -> frozenset[tuple[str, str, str]]:
  """Flows from an attacker to an agent the spec does not reach.

  The marker in the read is ground truth that the attacker's text got there, so each such flow
  is a path the recorders missed, such as a read served from a cache no seam sees.
  """
  bad = frozenset(attackers)
  reached = irspec.reach(to_spec(trace, bad, rules))
  return frozenset(f for f in flows(trace) if f[0] in bad and f[2] not in reached)


def shared_reads(trace: Trace) -> frozenset[tuple[str, str, str]]:
  """(marker principal, channel, reading agent) for every marker read of a channel outside a
  thread's state, within a principal too. A fix that stops a cross-principal flow by cutting
  the feature off shows up here as a missing same-principal read."""
  return frozenset((p, a.channel, a.agent) for a in trace.accesses
                   if a.mode == "read" and a.is_store
                   for p in owners(leaves(a.value), trace.markers))


def _same(x: Any, y: Any) -> bool:
  try:
    return bool(x == y)
  except Exception:  # noqa: BLE001, incomparable values count as different
    return False


def cross_reads(trace: Trace) -> frozenset[tuple[str, str, str, str]]:
  """(source principal, channel, reading agent, last writer) for reads markers cannot see.

  The last write to the channel before the read, in the same script and thread, came from a
  task serving another principal, and the value read carries none of its markers. A relay
  task writing back the value already there does not count as a new last write.
  """
  last: dict[tuple[str, str, str], Access] = {}
  found: set[tuple[str, str, str, str]] = set()
  for a in sorted(trace.accesses, key=lambda a: a.seq):
    where = (*a.scope, a.channel)
    if a.mode == "write":
      relay = (a.run, a.task) in trace.relays
      if where not in last or not (relay and _same(last[where].value, a.value)):
        last[where] = a
      continue
    w = last.get(where)
    if (w is not None and SHARED not in (w.principal, a.principal)
        and w.principal != a.principal
        and w.principal not in owners(leaves(a.value), trace.markers)):
      found.add((w.principal, a.channel, a.agent, w.agent))
  return frozenset(found)


# ---------------------------------------------------------------------------------------------
# Trace to ordered analysis input


LAST_VALUE = "LastValue"


@dataclass(frozen=True)
class NodeFacts:
  """What the trace shows about one node's tasks, for its flow summary.

  `kind` is `llm` when some task of the node called the fake LLM, `code` when none did and the
  node code of every task ran under a read proxy, and `opaque` otherwise (fallback, subgraph
  container or external task). `passes` holds the state keys every task of the node wrote, if
  at all, as a pass-through. `kills` holds the keys every task of the node wrote, never as a
  pass-through, to a `LastValue` channel of the node's own top-level graph that no other graph
  declares and only that graph's top-level nodes access.
  """
  kind: Literal["llm", "code", "opaque"]
  passes: frozenset[str] = frozenset()
  kills: frozenset[str] = frozenset()


def _node_tasks(trace: Trace) -> dict[str, set[tuple[str, str]]]:
  found: defaultdict[str, set[tuple[str, str]]] = defaultdict(set)
  for a in trace.accesses:
    found[a.node].add((a.run, a.task))
  return found


def node_facts(trace: Trace) -> dict[str, NodeFacts]:
  """`NodeFacts` of every node that has an access in the trace."""
  tasks = _node_tasks(trace)
  llm = ({node for _, _, node in trace.llm_tasks}
         | {node for node, ts in tasks.items() if any(r in trace.llm_lost for r, _ in ts)})
  writes: defaultdict[tuple[str, str], list[Access]] = defaultdict(list)
  users: defaultdict[str, set[str]] = defaultdict(set)
  for a in trace.accesses:
    if not a.is_store:
      users[a.channel].add(a.node)
      if a.mode == "write":
        writes[(a.node, a.channel)].append(a)
  def passed(a: Access) -> bool:
    return (a.run, a.task, a.channel) in trace.passes
  def own_last_value(node: str, key: str) -> bool:
    mine = [g for g in trace.graphs if node in g.nodes]
    return ("/" not in node and bool(mine)
            and all(g.channels.get(key) == LAST_VALUE for g in mine)
            and all(g in mine for g in trace.graphs if key in g.channels)
            and all("/" not in m and any(m in g.nodes for g in mine) for m in users[key]))
  facts: dict[str, NodeFacts] = {}
  for node, ts in tasks.items():
    if node in llm:
      facts[node] = NodeFacts("llm")
      continue
    if not all(t in trace.tracked and t not in trace.containers for t in ts):
      facts[node] = NodeFacts("opaque")
      continue
    keys = {k for (n, k) in writes if n == node}
    facts[node] = NodeFacts(
      "code",
      frozenset(k for k in keys if all(passed(a) for a in writes[(node, k)])),
      frozenset(k for k in keys
                if {(a.run, a.task) for a in writes[(node, k)]} == ts
                and not any(passed(a) for a in writes[(node, k)])
                and own_last_value(node, k)))
  return facts


@dataclass
class _Unit:
  """Tasks that form one turn (`multi` false, one task) or a cluster, with their live span."""
  tasks: list[tuple[str, str]]
  multi: bool
  span: tuple[int, int] | None
  anchor: int = 0


def _graph_units(trace: Trace, run: str, has_access: set[tuple[str, str]]) -> list[_Unit]:
  """A run's graph tasks in superstep order. Tasks sharing a superstep, and a task with the
  tasks of a subgraph it runs, form one cluster."""
  children: defaultdict[str | None, list[str]] = defaultdict(list)
  for (r, t), _ in trace.steps.items():
    if r == run:
      parent = trace.parents.get((r, t))
      children[parent if (r, parent) in trace.steps else None].append(t)
  def below(t: str) -> list[str]:
    return [t, *(d for c in children[t] for d in below(c))]
  units: list[_Unit] = []
  by_step: defaultdict[int, list[str]] = defaultdict(list)
  for t in children[None]:
    by_step[trace.steps[(run, t)]].append(t)
  for step in sorted(by_step):
    members = by_step[step]
    tasks = [(run, d) for t in sorted(members) for d in below(t)]
    kept = [t for t in tasks if t in has_access]
    if kept:
      spans = [trace.spans[t] for t in tasks if t in trace.spans]
      span = (min(a for a, _ in spans), max(b for _, b in spans)) if spans else None
      units.append(_Unit(kept, len(tasks) > 1, span))
  return units


def _schedule_units(trace: Trace, script: str, has_access: set[tuple[str, str]]
                    ) -> list[_Unit]:
  """A script's turns as units in time order, merged into clusters where live spans overlap.

  Graph tasks follow their supersteps, and external tasks their live spans. A graph unit with
  no live span cannot be placed against external tasks, so when its run has any, the whole run
  becomes one cluster.
  """
  runs = sorted({r for r, _ in has_access if script_of(r) == script},
                key=lambda r: _natural(r.partition(".")[2]))
  items: list[_Unit] = []
  last = 0
  for run in runs:
    graph = _graph_units(trace, run, has_access)
    ext = [_Unit([t], False, trace.spans.get(t)) for t in sorted(has_access)
           if t[0] == run and t not in trace.steps]
    lives = [u.span[0] for u in graph + ext if u.span]
    anchor = min(lives) if lives else last
    if ext and any(u.span is None for u in graph):
      spans = [u.span for u in graph + ext if u.span]
      whole = (min(a for a, _ in spans), max(b for _, b in spans)) if spans else None
      items.append(_Unit([t for u in graph + ext for t in u.tasks], True, whole, anchor))
      last = whole[1] if whole else anchor
      continue
    for u in graph:
      anchor = max(anchor, u.span[0]) if u.span else anchor
      u.anchor = anchor
    for u in ext:
      u.anchor = u.span[0] if u.span else anchor
    items += graph + ext
    last = max([anchor, *(u.span[1] for u in graph + ext if u.span)])
  order = sorted(range(len(items)), key=lambda i: (items[i].anchor, i))
  merged: list[_Unit] = []
  end: int | None = None
  for i in order:
    u = items[i]
    if merged and u.span and end is not None and u.span[0] <= end:
      merged[-1] = _Unit(merged[-1].tasks + u.tasks, True, merged[-1].span, merged[-1].anchor)
    else:
      merged.append(u)
      end = None
    if u.span:
      end = u.span[1] if end is None else max(end, u.span[1])
  return merged


def ordered_dict(trace: Trace, attackers: Iterable[str], rules: Rules = Rules()
                 ) -> dict[str, Any]:
  """The input of the ordered analysis (`ordered.py`). It holds
  - `spec`, the same spec as `spec_dict`,
  - `summaries`, per agent its kind, and for code agents the outputs whose dependencies are
    narrower than every input (`dep`, output board to input boards),
  - `schedules`, per script the tasks in time order, each a turn of its agent, as clusters of
    tasks whose accesses overlap in time, each turn with the boards it surely replaces,
  - `flows`, the concrete cross-principal marker reads, with their script.

  Sound summaries, under the extractor's coverage assumption (every turn behaves as some
  traced turn of its node does) and the assumption that a code node's writes depend only on
  what it reads through the proxy and the recorders.
  - A key a code node always writes as a pass-through holds the key's old value, so the output
    depends only on the boards of that key in that thread the agent reads. Other outputs depend
    on every input, and any input taints the agent itself, as under `Reach`.
  - A turn kills the boards of a key in `NodeFacts.kills` in its own thread, since the node
    always overwrites that `LastValue` channel with a value computed from its reads. A turn in
    a cluster of several tasks kills nothing, since another task may read the old value.
  - LLM nodes and opaque nodes are black boxes.
  """
  spec = spec_dict(trace, attackers, rules)
  located = list(located_roles(trace, rules))
  board_at: dict[str, tuple[str, str]] = {}
  read_at: defaultdict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
  for board, role, agent, at in located:
    if role == "writer":
      board_at[board] = at
    else:
      read_at[(agent, board)].add(at)
  facts = node_facts(trace)
  node_of = {a.agent: a.node for a in trace.accesses}
  summaries: dict[str, dict[str, Any]] = {}
  for agent in spec["agents"]:
    f = facts.get(node_of.get(agent, ""))
    if f is None:
      summaries[agent] = {"kind": "input" if agent.startswith("input@") else "opaque"}
      continue
    dep = {}
    if f.kind == "code":
      ins = [b for b in spec["boards"] if agent in spec["boards"][b]["readers"]]
      for out in (b for b in spec["boards"] if agent in spec["boards"][b]["writers"]):
        channel, thread = board_at[out]
        if channel in f.passes:
          dep[out] = sorted(i for i in ins if (channel, thread) in read_at[(agent, i)])
    summaries[agent] = {"kind": f.kind, "dep": dep, "passes": sorted(f.passes),
                        "kills": sorted(f.kills)}
  writes_of: defaultdict[str, list[str]] = defaultdict(list)
  for b, r in spec["boards"].items():
    for w in r["writers"]:
      writes_of[w].append(b)
  who: dict[tuple[str, str], Access] = {}
  for a in trace.accesses:
    who.setdefault((a.run, a.task), a)
  schedules = []
  for script in sorted({script_of(r) for r, _ in who}, key=_natural):
    turns = []
    for i, unit in enumerate(_schedule_units(trace, script, set(who))):
      for t in unit.tasks:
        a = who[t]
        f = facts[a.node]
        kills = [] if unit.multi or f.kind != "code" else sorted(
          b for b in writes_of[a.agent]
          if board_at[b][0] in f.kills and board_at[b][1] == a.thread)
        turns.append({"agent": a.agent, "run": t[0], "task": t[1], "cluster": i,
                      "kills": kills})
    schedules.append({"script": script, "turns": turns})
  raw = _raw_leaves(trace)
  flows_by_script = sorted({
    (p, a.channel, a.agent, script_of(a.run))
    for a in trace.accesses if a.mode == "read"
    for p in split_markers(a.value, raw.get(a.run, frozenset()), trace.markers)[1]
    if p != a.principal})
  return {"spec": spec, "summaries": summaries, "schedules": schedules,
          "flows": [list(f) for f in flows_by_script]}


def _natural(script: str) -> tuple[int, str]:
  return (int(script), "") if script.isdigit() else (1 << 30, script)


# ---------------------------------------------------------------------------------------------
# Debug events to trace


def _event(ev: Any) -> tuple[int, tuple[str, ...], Mapping[str, Any]]:
  """Accept a `Stamped` event, `(namespace, chunk)` from `subgraphs=True` and a bare chunk."""
  seq, ev = (ev.seq, ev.event) if isinstance(ev, Stamped) else (0, ev)
  if isinstance(ev, tuple) and len(ev) == 2 and isinstance(ev[0], tuple):
    return seq, ev[0], ev[1]
  return seq, (), ev


def _fields(value: Any) -> Iterable[tuple[str, Any]]:
  """A task input or result as (state key, value) pairs.

  LangGraph 1.x gives a dict, and 0.2 gives a list of (channel, value) writes.
  """
  match value:
    case Mapping():
      return value.items()
    case list() | tuple() if all(isinstance(w, tuple | list) and len(w) == 2 for w in value):
      return [(str(k), v) for k, v in value]
    case _ if callable(getattr(value, "model_dump", None)):
      return ((k, getattr(value, k)) for k in value.model_dump())
    case _ if dataclasses.is_dataclass(value) and not isinstance(value, type):
      return ((f.name, getattr(value, f.name)) for f in dataclasses.fields(value))
    case None:
      return ()
    case _:
      return [("<input>", value)]


def _is_state_key(key: str) -> bool:
  return not key.startswith("__") and ":" not in key


def _ns_parts(ns: Iterable[str]) -> list[tuple[str, str]]:
  """(node, task id) for each `node:task_id` segment of a namespace."""
  return [tuple(seg.split(":", 1)) if ":" in seg else (seg, "") for seg in ns]  # type: ignore


def task_id_of(checkpoint_ns: str) -> str | None:
  """The task id at the end of a `configurable.checkpoint_ns` string."""
  last = checkpoint_ns.split("|")[-1] if checkpoint_ns else ""
  return last.split(":", 1)[1] if ":" in last else None


PrincipalOf = Callable[[str, Any], str | None]


def _place_external(tasks: dict[str, tuple[str, str]], external: Iterable[ExternalTask],
                    principal: str | None) -> int:
  """Add external tasks to `tasks` in time order, and count those left unattributed."""
  orphans = 0
  for ext in sorted(external, key=lambda e: e.seq):
    if ext.principal is not None:
      tasks[ext.task] = (ext.node, ext.principal)
    elif ext.parent is None:
      tasks[ext.task] = (ext.node, principal or SHARED)
    elif ext.parent in tasks:
      tasks[ext.task] = (ext.node, tasks[ext.parent][1])
    else:
      orphans += 1
  return orphans


def built_reads(ops: Iterable[StoreOp], calls: Iterable[LLMCall],
                markers: Mapping[str, str]) -> list[StoreOp]:
  """Reads of `built:` channels by the LLM calls whose input contains what was built.

  A graph factory bakes values such as a system prompt into the graph it returns, so a node
  reads them from its closure, where no state proxy sees it. A call reads a `built:` write when
  a marker-carrying line of the written value occurs inside a string of the call's input.
  """
  built = [op for op in ops if op.mode == "write" and op.where.startswith(BUILT_PREFIX)]
  def carried(op: StoreOp) -> list[str]:
    return [ln for t in leaves(op.value) for ln in t.splitlines() if owners([ln], markers)]
  wanted = [(op, carried(op)) for op in built]
  found: list[StoreOp] = []
  for call in calls:
    texts = list(leaves(call.value))
    found.extend(StoreOp(call.task, (), "read", op.value, call.seq, op.where)
                 for op, needles in wanted
                 if any(n in t for n in needles for t in texts))
  return found


def trace_from_events(run: str, events: Iterable[Any], store_ops: Iterable[StoreOp],
                      markers: Mapping[str, str], run_input: Any = None,
                      principal: str | None = None,
                      principal_of: PrincipalOf | None = None,
                      reads: Iterable[ReadOp] | None = None,
                      tracked: Iterable[str] = (), thread: str = "",
                      relays: Iterable[str] = (), external: Iterable[ExternalTask] = (),
                      calls: Iterable[LLMCall] = (),
                      passes: Iterable[tuple[str, str]] = (),
                      spans: Iterable[tuple[str, int, int]] = ()) -> Trace:
  """A trace from `stream_mode="debug"` events, store and resource operations and tracked reads
  of one run.

  `tracked` holds the ids of tasks whose reads `reads` records. Other tasks fall back to their
  whole debug-event input, except tasks that only contain a subgraph's tasks. `relays` holds
  the ids of tasks that returned their state unchanged. `external` holds tasks that ran outside
  the graph, and `calls` the fake LLM's calls, which turn `built:` writes into reads and mark
  their tasks as LLM tasks. `passes` holds the (task id, key) of pass-through writes, and
  `spans` the (task id, start, end) of each call of tracked node or routing code.

  Event times can be late, since an adapter may collect a run's events before handing them
  on, so the ordered analysis orders a run's graph tasks by their superstep (`Trace.steps`)
  and places them against external tasks by live times only (`Trace.spans`), which come from
  code calls, tracked reads, store and resource ops and external task starts.
  """
  evs = [_event(ev) for ev in events]
  calls, external = list(calls), list(external)
  containers = {tid for _, ns, _ in evs for _, tid in _ns_parts(ns)}
  tracked_ids = frozenset(tracked)
  tasks: dict[str, tuple[str, str]] = {}
  accesses: list[Access] = []
  fallbacks: set[str] = set()

  def access(tid: str, who: tuple[str, str], channel: str, mode: Mode, value: Any,
             seq: int) -> Access:
    return Access(run, tid, who[0], who[1], channel, mode, value, thread, seq)

  steps: dict[tuple[str, str], int] = {}
  parent_of: dict[tuple[str, str], str] = {}
  for seq, ns, chunk in evs:
    kind, payload = chunk.get("type"), chunk.get("payload", {})
    if kind not in ("task", "task_result"):
      continue
    tid, parents = payload["id"], _ns_parts(ns)
    if kind == "task":
      steps[(run, tid)] = int(chunk.get("step") or 0)
      if parents:
        parent_of[(run, tid)] = parents[-1][1]
      node = "/".join([*(n for n, _ in parents), payload["name"]])
      parent = tasks.get(parents[-1][1]) if parents else None
      who = ((principal_of(node, payload.get("input")) if principal_of else None)
             or (parent[1] if parent else None) or principal or SHARED)
      tasks[tid] = (node, who)
      if tid in tracked_ids or tid in containers:
        continue
      fallbacks.add(agent_name(node, who))
      fields = _fields(payload.get("input"))
    else:
      fields = _fields(payload.get("result"))
    who = tasks.get(tid, (payload["name"], principal or SHARED))
    mode: Mode = "read" if kind == "task" else "write"
    accesses.extend(access(tid, who, k, mode, v, seq) for k, v in fields if _is_state_key(k))
  result_seq = {chunk["payload"]["id"]: seq for seq, _, chunk in evs
                if chunk.get("type") == "task_result"}
  read_ops = [op for op in reads or () if op.task is not None and _is_state_key(op.key)]
  placed_reads = [op for op in read_ops if op.task in tasks]
  accesses.extend(
    access(str(op.task), tasks[str(op.task)], op.key, "read", op.value,
           result_seq.get(str(op.task), op.seq) + 1 if op.route else op.seq)
    for op in placed_reads)
  orphans = _place_external(tasks, external, principal)
  store_ops = list(store_ops)
  ops = [*store_ops, *built_reads(store_ops, calls, markers)]
  placed = [op for op in ops if op.task in tasks]
  accesses.extend(access(str(op.task), tasks[str(op.task)], op.where, op.mode, op.value, op.seq)
                  for op in placed)
  ordered = tuple(sorted(accesses, key=lambda a: a.seq))
  lost = len(ops) - len(placed) + len(read_ops) - len(placed_reads) + orphans
  llm = frozenset((run, str(c.task), tasks[c.task][0]) for c in calls if c.task in tasks)
  live: defaultdict[tuple[str, str], list[int]] = defaultdict(list)
  for tid, lo, hi in spans:
    live[(run, tid)] += [lo, hi]
  for op in placed_reads:
    live[(run, str(op.task))].append(op.seq)
  for op in placed:
    live[(run, str(op.task))].append(op.seq)
  for ext in external:
    live[(run, ext.task)].append(ext.seq)
  return Trace(dict(markers), {run: run_input}, ordered, lost, frozenset(fallbacks),
               frozenset((run, t) for t in relays),
               tracked=frozenset((run, t) for t in tracked_ids if t in tasks),
               containers=frozenset((run, t) for t in containers if t in tasks),
               llm_tasks=llm,
               llm_lost=frozenset({run} if any(c.task not in tasks for c in calls) else ()),
               passes=frozenset((run, t, k) for t, k in passes if t in tasks),
               steps=steps, parents=parent_of,
               spans={t: (min(v), max(v)) for t, v in live.items() if t[1] in tasks})


# ---------------------------------------------------------------------------------------------
# Fake LLM scripts


Script = Mapping[str, Any]


def seq(*responses: Any) -> Callable[[int], Any]:
  """A scripted response per call, repeating the last one."""
  return lambda i: responses[min(i, len(responses) - 1)]


def router_scripts(choices: Mapping[str, Sequence[Any]]) -> tuple[dict[str, Any], ...]:
  """Every combination of one choice per router key."""
  keys = list(choices)
  combos = itertools.product(*choices.values())
  return tuple(dict(zip(keys, combo, strict=True)) for combo in combos)


def fill(template: Any, seen: str) -> Any:
  """`template` with `{markers}` replaced by `seen` in every string."""
  match template:
    case str():
      return template.replace("{markers}", seen)
    case Mapping():
      return {k: fill(v, seen) for k, v in template.items()}
    case list() | tuple():
      return type(template)(fill(v, seen) for v in template)
    case _:
      return template


@functools.cache
def _marker_llm_class() -> type:
  from langchain_core.language_models.chat_models import BaseChatModel
  from langchain_core.messages import AIMessage
  from langchain_core.outputs import ChatGeneration, ChatResult
  from langchain_core.runnables import RunnableLambda
  from pydantic import PrivateAttr

  class MarkerLLM(BaseChatModel):
    """A chat model that copies every marker it sees into its scripted reply."""
    markers: dict[str, str]
    script: dict[str, Any] = {}
    _calls: dict[str, int] = PrivateAttr(default_factory=dict)
    _lock: Any = PrivateAttr(default_factory=threading.Lock)

    @property
    def _llm_type(self) -> str:
      return "marker-echo"

    def seen(self, value: Any) -> str:
      return " ".join(m for m in self.markers.values() if any(m in t for t in leaves(value)))

    def next(self, key: str, default: Any) -> Any:
      with self._lock:
        i = self._calls.get(key, 0)
        self._calls[key] = i + 1
      r = self.script.get(key, default)
      return r(i) if callable(r) else r

    def _generate(self, messages, stop=None, run_manager=None, **kwargs) -> ChatResult:
      RESOURCES.add_call(LLMCall(current_task(), _snapshot(messages), tick()))
      seen = self.seen(messages)
      text = self.next("text", "[fake]")
      calls = fill(self.next("tool_calls", []), seen)
      reply = AIMessage(
        content=fill(text, seen) if "{markers}" in text else f"{text} {seen}".strip(),
        tool_calls=[{"name": c["name"], "args": c.get("args", {}),
                     "id": c.get("id", f"call_{uuid.uuid4().hex[:8]}")} for c in calls])
      return ChatResult(generations=[ChatGeneration(message=reply)])

    def bind_tools(self, tools, **kwargs):
      return self

    def structured(self, schema: Any, value: Any) -> Any:
      RESOURCES.add_call(LLMCall(current_task(), _snapshot(value), tick()))
      seen = self.seen(value)
      name = schema.get("title", "") if isinstance(schema, Mapping) else schema.__name__
      chosen = fill(self.next(name, {}), seen)
      if isinstance(schema, Mapping):
        props = schema.get("properties", {})
        return {k: chosen.get(k, f"[fake] {seen}") for k in props
                if k in chosen or props[k].get("type") == "string"}
      if hasattr(schema, "model_fields"):
        unset = {k: f"[fake] {seen}" for k, f in schema.model_fields.items()
                 if k not in chosen and f.annotation is str}
        return schema.model_validate({**unset, **chosen})
      from typing import get_type_hints
      hints = get_type_hints(schema)
      return {**{k: f"[fake] {seen}" for k, t in hints.items() if t is str}, **chosen}

    def with_structured_output(self, schema, *, include_raw: bool = False, **kwargs):
      def run(value: Any) -> Any:
        out = self.structured(schema, value)
        return {"raw": None, "parsed": out, "parsing_error": None} if include_raw else out
      return RunnableLambda(run)

  return MarkerLLM


def marker_llm(markers: Mapping[str, str], script: Script | None = None) -> Any:
  """A LangChain chat model that copies markers and follows `script` (module docstring)."""
  return _marker_llm_class()(markers=dict(markers), script=dict(script or {}))


# ---------------------------------------------------------------------------------------------
# Read tracking


_COUNTER = itertools.count(1)


def tick() -> int:
  """The next even time on the clock shared by events, reads and store operations."""
  return 2 * next(_COUNTER)


def _snapshot(value: Any) -> Any:
  """A deep copy, since recorded values alias channel values that later nodes may mutate in
  place (kaymen99 pops `emails` in a routing function)."""
  try:
    return copy.deepcopy(value)
  except Exception:  # noqa: BLE001, an uncopyable value is recorded as is
    return value


@dataclass
class ReadLog:
  """Every tracked access, the tasks whose node code ran under tracking, and those of them that
  returned their state unchanged."""
  reads: list[ReadOp] = field(default_factory=list)
  tasks: list[str] = field(default_factory=list)
  relays: list[str] = field(default_factory=list)
  passes: list[tuple[str, str]] = field(default_factory=list)
  spans: list[tuple[str, int, int]] = field(default_factory=list)
  lock: Any = field(default_factory=threading.Lock)

  def add_read(self, op: ReadOp) -> None:
    with self.lock:
      self.reads.append(op)

  def add_task(self, task: str) -> None:
    with self.lock:
      self.tasks.append(task)

  def add_relay(self, task: str) -> None:
    with self.lock:
      self.relays.append(task)

  def add_passes(self, task: str, keys: Iterable[str]) -> None:
    with self.lock:
      self.passes.extend((task, k) for k in keys)

  def add_span(self, task: str, opened: int, closed: int) -> None:
    with self.lock:
      self.spans.append((task, opened, closed))


READ_LOG = ReadLog()


@dataclass
class _Session:
  """One tracked call of node or routing code. Accesses after the call returns are LangGraph's
  own and are not recorded. A node call also keeps the state's values as it got them, and a
  deep copy of each, to find its pass-through writes."""
  task: str
  route: bool
  live: bool = True
  given: dict[str, Any] = field(default_factory=dict)
  copies: dict[str, Any] = field(default_factory=dict)

  def record(self, key: str, value: Any) -> None:
    if self.live:
      READ_LOG.add_read(ReadOp(self.task, key, _snapshot(value), tick(), self.route))


class TrackedDict(dict):
  """A dict state that records each key whose value node code reads.

  Overriding `__iter__` makes CPython's `{**d}`, `dict(d)` and `update(d)` go through `keys`
  and `__getitem__`, so they record every key too.
  """
  __slots__ = ("_lg",)

  def __init__(self, data: Mapping[str, Any], session: _Session) -> None:
    dict.__init__(self, data)
    self._lg = session

  def _all(self) -> dict[str, Any]:
    plain = dict(dict.items(self))
    for k, v in plain.items():
      self._lg.record(k, v)
    return plain

  def __getitem__(self, key: str) -> Any:
    value = dict.__getitem__(self, key)
    self._lg.record(key, value)
    return value

  def get(self, key: str, default: Any = None) -> Any:
    return self[key] if dict.__contains__(self, key) else default

  def setdefault(self, key: str, default: Any = None) -> Any:
    if dict.__contains__(self, key):
      return self[key]
    dict.__setitem__(self, key, default)
    return default

  def pop(self, key: str, *default: Any) -> Any:
    if dict.__contains__(self, key):
      self._lg.record(key, dict.__getitem__(self, key))
    return dict.pop(self, key, *default)

  def popitem(self) -> tuple[str, Any]:
    key, value = dict.popitem(self)
    self._lg.record(key, value)
    return key, value

  def __iter__(self) -> Iterator[str]:
    return dict.__iter__(self)

  def items(self) -> Any:
    return self._all().items()

  def values(self) -> Any:
    return self._all().values()

  def copy(self) -> dict[str, Any]:
    return self._all()

  __copy__ = copy

  def __deepcopy__(self, memo: dict[int, Any]) -> dict[str, Any]:
    return copy.deepcopy(self._all(), memo)

  def __reduce_ex__(self, protocol: Any) -> Any:
    return dict, (self._all(),)

  def __or__(self, other: Any) -> Any:
    return self._all() | other

  def __ror__(self, other: Any) -> Any:
    return other | self._all()

  def __eq__(self, other: object) -> bool:
    return self._all() == other

  def __ne__(self, other: object) -> bool:
    return self._all() != other

  __hash__ = None  # type: ignore[assignment]

  def __repr__(self) -> str:
    return repr(self._all())

  def unwrap(self) -> dict[str, Any]:
    return dict(dict.items(self))


WHOLE_STATE_METHODS = frozenset({"model_dump", "model_dump_json", "dict", "json", "model_copy",
                                 "copy", "__dict__"})


def _field_names(obj: Any) -> frozenset[str]:
  fields = getattr(type(obj), "model_fields", None) or getattr(type(obj), "__fields__", None)
  if fields is not None:
    return frozenset(fields)
  if dataclasses.is_dataclass(obj) and not isinstance(obj, type):
    return frozenset(f.name for f in dataclasses.fields(obj))
  return frozenset()


class TrackedObject:
  """A pydantic or dataclass state that records each field node code reads. It forwards every
  other attribute, and reports the state's class as its own so `isinstance` checks pass."""
  __slots__ = ("_lg_obj", "_lg", "_lg_fields")

  def __init__(self, obj: Any, session: _Session) -> None:
    object.__setattr__(self, "_lg_obj", obj)
    object.__setattr__(self, "_lg", session)
    object.__setattr__(self, "_lg_fields", _field_names(obj))

  @property  # type: ignore[misc]
  def __class__(self) -> type:  # noqa: D105
    return type(object.__getattribute__(self, "_lg_obj"))

  def __getattr__(self, name: str) -> Any:
    obj = object.__getattribute__(self, "_lg_obj")
    session = object.__getattribute__(self, "_lg")
    value = getattr(obj, name)
    if name in object.__getattribute__(self, "_lg_fields"):
      session.record(name, value)
    elif name in WHOLE_STATE_METHODS:
      for f in object.__getattribute__(self, "_lg_fields"):
        session.record(f, getattr(obj, f))
    return value

  def __setattr__(self, name: str, value: Any) -> None:
    setattr(object.__getattribute__(self, "_lg_obj"), name, value)

  def __getitem__(self, key: str) -> Any:
    return getattr(self, key)

  def __repr__(self) -> str:
    return repr(object.__getattribute__(self, "_lg_obj"))

  def unwrap(self) -> Any:
    return object.__getattribute__(self, "_lg_obj")


_UNCOPIED = object()


def _copy_or_mark(value: Any) -> Any:
  try:
    return copy.deepcopy(value)
  except Exception:  # noqa: BLE001, an uncopyable value can never count as unchanged
    return _UNCOPIED


def state_values(state: Any) -> dict[str, Any]:
  """The state's values by key, for a dict or a pydantic or dataclass state, untracked."""
  if isinstance(state, TrackedDict | TrackedObject):
    state = state.unwrap()
  if isinstance(state, Mapping):
    return dict(dict.items(state)) if isinstance(state, dict) else dict(state.items())
  return {k: getattr(state, k) for k in _field_names(state) if hasattr(state, k)}


def pass_through_keys(out: Any, proxy: Any, given: Mapping[str, Any],
                      copies: Mapping[str, Any]) -> list[str]:
  """Keys whose written value is the very object the state held for that key when the node was
  called, equal to its copy taken then, so unchanged in place.

  Such a write copies the key's old value and nothing else. The update is the returned
  mapping, a `Command`'s mapping update, or the whole state when the node returned it.
  """
  if out is proxy:
    update: Any = state_values(proxy)
  elif isinstance(out, Mapping):
    update = out
  else:
    update = getattr(out, "update", None)
    if not isinstance(update, Mapping):
      return []
  return [k for k, v in update.items()
          if k in given and v is given[k] and copies.get(k, _UNCOPIED) is not _UNCOPIED
          and _same(v, copies[k])]


def tracking_proxy(state: Any, session: _Session) -> TrackedDict | TrackedObject | None:
  """A proxy recording reads of `state`, or None when its shape cannot be tracked."""
  if isinstance(state, dict):
    return TrackedDict(state, session)
  if _field_names(state):
    return TrackedObject(state, session)
  return None


def _config_task(config: Any) -> str | None:
  conf = (config or {}).get("configurable", {}) if isinstance(config, Mapping) else {}
  return task_id_of(conf.get("checkpoint_ns", ""))


@functools.cache
def _tracked_runnable_class() -> type:
  from langchain_core.runnables import Runnable

  class TrackedRunnable(Runnable):
    """Node or routing code that gets the state through a tracking proxy."""

    def __init__(self, inner: Any, route: bool) -> None:
      self.inner = inner
      self.route = route
      self.name = getattr(inner, "name", None)

    def _open(self, state: Any, config: Any) -> tuple[Any, _Session | None]:
      task = _config_task(config)
      session = _Session(task, self.route) if task else None
      proxy = tracking_proxy(state, session) if session else None
      if proxy is None:
        return state, None
      if not self.route:
        READ_LOG.add_task(session.task)
        session.given = state_values(proxy)
        session.copies = {k: _copy_or_mark(v) for k, v in session.given.items()}
      return proxy, session

    @staticmethod
    def _close(out: Any, proxy: Any, session: _Session | None) -> Any:
      if session is None:
        return out
      session.live = False
      if not session.route:
        READ_LOG.add_passes(session.task,
                            pass_through_keys(out, proxy, session.given, session.copies))
      if out is not proxy:
        return out
      READ_LOG.add_relay(session.task)
      return proxy.unwrap()

    def invoke(self, input: Any, config: Any = None, **kwargs: Any) -> Any:
      task, opened = _config_task(config), tick()
      proxy, session = self._open(input, config)
      try:
        out = self.inner.invoke(proxy, config, **kwargs)
      finally:
        if session:
          session.live = False
        if task:
          READ_LOG.add_span(task, opened, tick())
      return self._close(out, proxy, session)

    async def ainvoke(self, input: Any, config: Any = None, **kwargs: Any) -> Any:
      task, opened = _config_task(config), tick()
      proxy, session = self._open(input, config)
      try:
        out = await self.inner.ainvoke(proxy, config, **kwargs)
      finally:
        if session:
          session.live = False
        if task:
          READ_LOG.add_span(task, opened, tick())
      return self._close(out, proxy, session)

  return TrackedRunnable


def _replace(spec: Any, **changes: Any) -> Any:
  """A node or branch spec with fields changed, whether a NamedTuple (0.x) or a dataclass."""
  return spec._replace(**changes) if hasattr(spec, "_replace") else dataclasses.replace(
    spec, **changes)


COMPILE_ATTRS = {"checkpointer": "checkpointer", "store": "store", "cache": "cache",
                 "interrupt_before": "interrupt_before_nodes",
                 "interrupt_after": "interrupt_after_nodes", "debug": "debug", "name": "name"}


GRAPHS: list[Graph] = []


def _recompiled(graph: Any) -> Any:
  """A compiled subgraph rebuilt from its instrumented builder with its own compile settings."""
  return instrument_compiled(graph)


def _track(runnable: Any, route: bool) -> Any:
  from langgraph.pregel import Pregel
  if isinstance(runnable, _tracked_runnable_class()):
    return runnable
  if isinstance(runnable, Pregel) and hasattr(runnable, "builder"):
    return _recompiled(runnable)
  return _tracked_runnable_class()(runnable, route)


def instrument_compiled(graph: Any, **overrides: Any) -> Any:
  """A compiled graph, such as one from langchain's `create_agent`, recompiled from its own
  builder instrumented, with its compile settings except those in `overrides`."""
  builder = instrument(graph.builder)
  accepted = inspect.signature(builder.compile).parameters
  settings = {arg: getattr(graph, attr) for arg, attr in COMPILE_ATTRS.items()
              if arg in accepted and hasattr(graph, attr)}
  return builder.compile(**{**settings, **overrides})


def instrument(builder: Any) -> Any:
  """A copy of `StateGraph` `builder` whose nodes and routing functions record their reads.

  Compile the copy instead of `builder`. The original builder is left unchanged.
  """
  new = copy.copy(builder)
  GRAPHS.append(Graph(frozenset(builder.nodes), {
    k: type(ch).__name__ for k, ch in (getattr(builder, "channels", None) or {}).items()}))
  new.nodes = {k: _replace(spec, runnable=_track(spec.runnable, False))
               for k, spec in builder.nodes.items()}
  new.branches = defaultdict(dict, {
    src: {name: _replace(b, path=_track(b.path, True)) for name, b in bs.items()}
    for src, bs in builder.branches.items()})
  return new


# ---------------------------------------------------------------------------------------------
# Resources outside LangGraph


@dataclass
class ResourceLog:
  """Resource ops, external tasks and fake-LLM calls, from any thread."""
  ops: list[StoreOp] = field(default_factory=list)
  tasks: list[ExternalTask] = field(default_factory=list)
  calls: list[LLMCall] = field(default_factory=list)
  lock: Any = field(default_factory=threading.Lock)

  def add_op(self, op: StoreOp) -> None:
    with self.lock:
      self.ops.append(op)

  def add_task(self, task: ExternalTask) -> None:
    with self.lock:
      self.tasks.append(task)

  def add_call(self, call: LLMCall) -> None:
    with self.lock:
      self.calls.append(call)

  def mark(self) -> tuple[int, int, int]:
    with self.lock:
      return len(self.ops), len(self.tasks), len(self.calls)

  def since(self, mark: tuple[int, int, int]) -> tuple[list[StoreOp], list[ExternalTask],
                                                       list[LLMCall]]:
    with self.lock:
      return self.ops[mark[0]:], self.tasks[mark[1]:], self.calls[mark[2]:]


RESOURCES = ResourceLog()
_ACTOR: contextvars.ContextVar[str | None] = contextvars.ContextVar("lgtrace_actor", default=None)


def _current_task() -> str | None:
  """The LangGraph task whose config is current, if LangGraph is installed and in a task."""
  try:
    from langgraph.config import get_config
  except ImportError:
    return None
  try:
    conf = get_config()
  except RuntimeError:
    return None
  return task_id_of(conf.get("configurable", {}).get("checkpoint_ns", ""))


def current_task() -> str | None:
  """The task an access belongs to, an open external task first, else the LangGraph task.

  The external task wins because it can run inside a node, as an updater called from a node
  does, and then it, not the node, is the actor.
  """
  return _ACTOR.get() or _current_task()


_INHERIT: Any = object()


@contextlib.contextmanager
def acting(node: str, principal: str | None = None, parent: str | None = _INHERIT
           ) -> Iterator[str]:
  """Run the body as external task `node`, yielding its id.

  `parent` defaults to the current task. The id lives in a context variable, so it follows the
  body into `asyncio` tasks and `asyncio.to_thread`, but not into a `threading.Thread` or a
  `ThreadPoolExecutor`, which start from an empty context. Code that hands work to those
  carries the attribution across with a `Handoff`.
  """
  tid = f"ext-{uuid.uuid4().hex[:12]}"
  RESOURCES.add_task(ExternalTask(tid, node, principal,
                                  current_task() if parent is _INHERIT else parent, tick()))
  token = _ACTOR.set(tid)
  try:
    yield tid
  finally:
    _ACTOR.reset(token)


def emit(channel: str, mode: Mode, value: Any) -> None:
  """Record one access of resource `channel` by the current task."""
  RESOURCES.add_op(StoreOp(current_task(), (), mode, _snapshot(value), tick(), channel))


@dataclass
class Handoff:
  """Carries attribution across a queue or thread boundary that context variables do not cross.

  The producer calls `send(key, value)` in its own task, which records a write of `channel`
  and remembers the task under `key`. The consumer runs `with receive(key, node, value)`, in
  any thread, which opens external task `node` acting for the remembered task and records its
  read of `channel`. A later `send` with the same key replaces the earlier one, as a queue that
  merges entries per key does.
  """
  channel: str
  senders: dict[Any, str | None] = field(default_factory=dict)
  lock: Any = field(default_factory=threading.Lock)

  def send(self, key: Any, value: Any) -> None:
    emit(self.channel, "write", value)
    with self.lock:
      self.senders[key] = current_task()

  @contextlib.contextmanager
  def receive(self, key: Any, node: str, value: Any) -> Iterator[str]:
    with self.lock:
      parent = self.senders.get(key)
    with acting(node, parent=parent) as tid:
      emit(self.channel, "read", value)
      yield tid


def recorded(fn: Callable[..., Any], mode: Mode, channel: Callable[..., str],
             value: Callable[[tuple[Any, ...], dict[str, Any], Any], Any] | None = None
             ) -> Callable[..., Any]:
  """`fn`, which also records one access per call of `channel(*args, **kwargs)`.

  The value recorded is `value(args, kwargs, result)`, by default the result for a read and
  the first argument after `self` for a write. Use it to wrap an app's storage class at its
  own interface, above any cache the app keeps in memory.
  """
  def pick(args: tuple[Any, ...], kwargs: dict[str, Any], result: Any) -> Any:
    if value is not None:
      return value(args, kwargs, result)
    return result if mode == "read" else (args[1] if len(args) > 1 else None)

  if inspect.iscoroutinefunction(fn):
    @functools.wraps(fn)
    async def awrapper(*args: Any, **kwargs: Any) -> Any:
      result = await fn(*args, **kwargs)
      emit(channel(*args, **kwargs), mode, pick(args, kwargs, result))
      return result
    return awrapper

  @functools.wraps(fn)
  def wrapper(*args: Any, **kwargs: Any) -> Any:
    result = fn(*args, **kwargs)
    emit(channel(*args, **kwargs), mode, pick(args, kwargs, result))
    return result
  return wrapper


_HOOK_GUARD = threading.local()
_FILE_RECORDERS: list[FileRecorder] = []
_HOOK_LOCK = threading.Lock()


def _audit(event: str, args: tuple[Any, ...]) -> None:
  if event not in ("open", "os.rename", "os.remove") or not _FILE_RECORDERS:
    return
  if getattr(_HOOK_GUARD, "busy", False):
    return
  _HOOK_GUARD.busy = True
  try:
    for rec in list(_FILE_RECORDERS):
      rec.on_event(event, args)
  finally:
    _HOOK_GUARD.busy = False


def _install_audit_hook() -> None:
  with _HOOK_LOCK:
    if not getattr(sys, "_lgtrace_audit", False):
      sys.addaudithook(_audit)
      sys._lgtrace_audit = True  # type: ignore[attr-defined]


def _writes(mode: Any, flags: Any) -> bool:
  if isinstance(mode, str):
    return any(c in mode for c in "wax+")
  return bool(isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR))


class FileRecorder:
  """Records file accesses under `root` as resource ops on `file:<path below root>`.

  The seam is CPython's audit hooks (PEP 578). The `open` event fires for `open`, `io.open`,
  `Path.open`, `Path.read_text` and `os.open`, and `os.rename` for `os.rename`, `os.replace`
  and `Path.replace`, whatever library makes the call. An open for reading records the file's
  content at that moment. An open for writing records nothing yet, since the content is not
  written. It is recorded, for the opening task, when someone next opens the file, when it is
  renamed (then under the new name, which is how atomic saves through a temporary file work),
  and when the recorder closes. A `.json` file is recorded parsed, so its strings are leaves.

  What it cannot see. Reads served from an in-process cache never open the file, so wrap the
  app's storage interface with `recorded` when the app caches. Native code that does its own
  I/O (sqlite, mmap) raises no `open` event for Python's hook.
  """

  def __init__(self, root: str | os.PathLike[str]) -> None:
    self.root = os.path.realpath(root)
    self.pending: dict[str, str | None] = {}
    self.lock = threading.Lock()

  def __enter__(self) -> FileRecorder:
    _install_audit_hook()
    with _HOOK_LOCK:
      _FILE_RECORDERS.append(self)
    return self

  def __exit__(self, *exc: Any) -> None:
    with _HOOK_LOCK:
      _FILE_RECORDERS.remove(self)
    self.flush()

  def rel(self, path: Any) -> str | None:
    if isinstance(path, int) or path is None:
      return None
    try:
      full = os.path.realpath(os.fsdecode(path))
    except (TypeError, ValueError):
      return None
    if full != self.root and not full.startswith(self.root + os.sep):
      return None
    return os.path.relpath(full, self.root)

  def content(self, rel: str, name: str | None = None) -> Any:
    """`rel`'s content, parsed when `name` (by default `rel`) is a `.json` file."""
    full = os.path.join(self.root, rel)
    try:
      with open(full, "rb") as f:
        data = f.read()
    except OSError:
      return None
    text = data.decode(errors="replace")
    if (name or rel).endswith(".json"):
      try:
        return json.loads(text)
      except ValueError:
        return text
    return text

  def _land(self, rel: str, task: str | None, target: str | None = None) -> None:
    """Record the write of `rel`'s current content, for `task`, under `target` or `rel`."""
    RESOURCES.add_op(StoreOp(task, (), "write", self.content(rel, target), tick(),
                             FILE_PREFIX + (target or rel)))

  def on_event(self, event: str, args: tuple[Any, ...]) -> None:
    if event == "open":
      path, mode, flags = (tuple(args) + (None, None, None))[:3]
      rel = self.rel(path)
      if rel is None or os.path.isdir(os.path.join(self.root, rel)):
        return
      with self.lock:
        if rel in self.pending:
          self._land(rel, self.pending.pop(rel))
        if _writes(mode, flags):
          self.pending[rel] = current_task()
          if not (isinstance(mode, str) and "r" in mode):
            return
      if os.path.exists(os.path.join(self.root, rel)):
        RESOURCES.add_op(StoreOp(current_task(), (), "read", self.content(rel), tick(),
                                 FILE_PREFIX + rel))
    elif event == "os.rename":
      src, dst = self.rel(args[0]), self.rel(args[1])
      with self.lock:
        task = self.pending.pop(src, current_task()) if src else current_task()
        if src is not None and dst is not None:
          self._land(src, task, dst)
    elif event == "os.remove":
      rel = self.rel(args[0])
      if rel is not None:
        with self.lock:
          self.pending.pop(rel, None)
        RESOURCES.add_op(StoreOp(current_task(), (), "write", None, tick(), FILE_PREFIX + rel))

  def flush(self) -> None:
    """Record every write still pending."""
    _HOOK_GUARD.busy = True
    try:
      with self.lock:
        for rel, task in list(self.pending.items()):
          self._land(rel, task)
        self.pending.clear()
    finally:
      _HOOK_GUARD.busy = False


# ---------------------------------------------------------------------------------------------
# LangGraph hooks


@functools.cache
def _recording_store_class() -> type:
  from langgraph.store.base import BaseStore, GetOp, PutOp, SearchOp

  class RecordingStore(BaseStore):
    """A store that forwards to `inner` and logs each get, search and put with its task."""

    def __init__(self, inner: BaseStore) -> None:
      self.inner = inner
      self.ops: list[StoreOp] = []
      self.supports_ttl = getattr(inner, "supports_ttl", False)  # absent before langgraph 0.3
      self.ttl_config = getattr(inner, "ttl_config", None)

    def __getattr__(self, name: str) -> Any:
      return getattr(self.__dict__["inner"], name)

    def _record(self, ops: Iterable[Any], results: list[Any]) -> list[Any]:
      task = current_task()
      for op, res in zip(ops, results, strict=True):
        match op:
          case GetOp():
            self.ops.append(StoreOp(task, tuple(op.namespace), "read", res, tick()))
          case SearchOp():
            self.ops.extend(StoreOp(task, tuple(it.namespace), "read", it, tick())
                            for it in res or [])
          case PutOp():
            self.ops.append(StoreOp(task, tuple(op.namespace), "write", op.value, tick()))
      return results

    def batch(self, ops: Iterable[Any]) -> list[Any]:
      ops = list(ops)
      return self._record(ops, self.inner.batch(ops))

    async def abatch(self, ops: Iterable[Any]) -> list[Any]:
      ops = list(ops)
      return self._record(ops, await self.inner.abatch(ops))

  return RecordingStore


def recording_store(inner: Any = None) -> Any:
  """A `RecordingStore` around `inner`, a fresh `InMemoryStore` by default."""
  if inner is None:
    from langgraph.store.memory import InMemoryStore
    inner = InMemoryStore()
  return _recording_store_class()(inner)


@dataclass(frozen=True)
class Run:
  input: Any
  principal: str | None = None
  config: Mapping[str, Any] | None = None
  resumes: tuple[Any, ...] = ()


def thread_of(run: Run, index: int) -> str:
  """The run's `configurable.thread_id`, or `run<index>` when it has none."""
  tid = ((run.config or {}).get("configurable") or {}).get("thread_id")
  return str(tid) if tid is not None else f"run{index}"


def run_trace(graph: Any, run: Run, store: Any, markers: Mapping[str, str], run_id: str = "0",
              principal_of: PrincipalOf | None = None, thread: str = "") -> Trace:
  """Stream `run` through `graph` in debug mode and attribute every task, read and store op."""
  from langgraph.types import Command
  start, reads_start = len(store.ops), len(READ_LOG.reads)
  tasks_start, relays_start = len(READ_LOG.tasks), len(READ_LOG.relays)
  passes_start, spans_start = len(READ_LOG.passes), len(READ_LOG.spans)
  mark = RESOURCES.mark()
  config = dict(run.config or {})
  inputs = [run.input, *(Command(resume=r) for r in run.resumes)]
  events = [Stamped(tick(), _snapshot(ev)) for inp in inputs
            for ev in graph.stream(inp, config, stream_mode="debug", subgraphs=True)]
  ops, external, calls = RESOURCES.since(mark)
  return trace_from_events(run_id, events, [*store.ops[start:], *ops], markers, run.input,
                           run.principal, principal_of, READ_LOG.reads[reads_start:],
                           READ_LOG.tasks[tasks_start:], thread, READ_LOG.relays[relays_start:],
                           external, calls, READ_LOG.passes[passes_start:],
                           READ_LOG.spans[spans_start:])


@dataclass(frozen=True)
class Subject:
  build: Callable[[Any, Script], Any]
  runs: Sequence[Run]
  markers: Mapping[str, str]
  attackers: frozenset[str]
  scripts: Sequence[Script] = ({},)
  principal_of: PrincipalOf | None = None
  store: Callable[[], Any] | None = None


def trace_subject(subject: Subject) -> Trace:
  """One trace per router script, each with a fresh store and graph, merged."""
  def per_script(i: int, script: Script) -> Trace:
    store = recording_store(subject.store() if subject.store else None)
    graph = subject.build(store, script)
    return functools.reduce(Trace.__add__, (
      run_trace(graph, run, store, subject.markers, f"{i}.{j}", subject.principal_of,
                thread_of(run, j))
      for j, run in enumerate(subject.runs)), Trace(dict(subject.markers)))
  graphs_start = len(GRAPHS)
  trace = functools.reduce(Trace.__add__, itertools.starmap(per_script,
                                                            enumerate(subject.scripts)))
  trace = dataclasses.replace(trace, graphs=tuple(
    {g.key(): g for g in GRAPHS[graphs_start:]}.values()))
  if trace.fallbacks:
    warnings.warn(f"reads not tracked, whole input used: {sorted(trace.fallbacks)}",
                  stacklevel=2)
  return trace


def extract(subject: Subject) -> irspec.Spec:
  return to_spec(trace_subject(subject), subject.attackers)
