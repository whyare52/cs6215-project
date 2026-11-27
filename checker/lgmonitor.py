"""Runtime monitor that makes every run of a LangGraph app conform to a configuration.

The extractor (`lgtrace`) proposes a configuration from traced runs and Lean proves it safe.
This module enforces that configuration on every run, traced or not, at the seams `lgtrace`
records through. A channel the traces missed then shows up as a masked or flagged access
instead of a silent leak.

Provenance
- Every value written through a seam gets a label, the set of agents `node@P` that wrote it.
  A store item, a storage location or a file is overwritten, so its label is its last writer.
  A state key with a reducer may append, so its label is the union of its writers in the
  thread, and a key whose channel keeps the last value takes its last writer. The run input
  of principal `P` is written by `input@P`.
- On every read through a seam the reader is the current agent, and each writer in the value's
  label must be allowed for it by the policy. A value with no label (never written through a
  seam, such as a file that predates the run) is allowed and counted as unlabelled.

Policies
- `Isolation(shared=...)`. An agent serving `P` reads a value only if every writer served `P`,
  or the channel matches a pattern the configuration marks as shared by design.
- `SpecPolicy.from_spec(spec)`, an irspec configuration whose agents are `node@P` with each
  board's readers and writers, as `lgtrace` writes it. At `level="principal"` (the default) a
  board `c#..` with writer `w@P` and reader `r@Q` allows channel `c` from `P` to `Q`, and a
  principal's own flows are allowed, so `deerflow-fixed.json` is isolation with no shared
  channel. At `level="agent"` the (channel, writer, reader) triple must be in the spec, and a
  write needs its writer among the channel's writers.

Modes
- `block` replaces a disallowed value by what the reader's view holds, which is the
  `mask_view` law of `Ir/Refinement.lean`. Seams that can substitute (storage and store) give
  the latest value written by a writer the reader may read, and otherwise the blank of the
  value (`blank`). Seams that cannot substitute make the value absent: a file read raises
  `FileNotFoundError`. A write the policy forbids is skipped, as `guard` skips an action.
- `flag` records the violation and lets the access through.
- `raise` raises `MonitorViolation` at the access.

Seams, each the monitoring twin of an `lgtrace` recorder
- State keys, `monitor_graph` / `monitor_compiled`, which wrap every node and routing function
  of a `StateGraph` as `lgtrace.instrument` does and hand the node a masked copy of the state
  behind `lgtrace.TrackedDict` / `TrackedObject`, so only keys the node reads count.
- Store items, `monitored_store(inner, monitor)`, per (namespace, key).
- An app's own storage methods, `guarded(fn, ...)`, the twin of `lgtrace.recorded`.
- Files, `MonitoredFiles(root, monitor)`, on CPython audit hooks as `lgtrace.FileRecorder`.
  It also reports process spawns and native database opens, which bypass the hook.
- Thread hand-offs, `MonitoredHandoff`, an `lgtrace.Handoff` that also carries the monitor's
  actor into the receiving thread, so a `threading.Timer` or executor keeps its principal.
- Prompts baked by a graph factory, `Monitor.built` (write) and the `built_readers` nodes of
  `monitor_graph` (read on every call).

Attribution. The current actor is a context variable set by `Monitor.serving(P)` around a run,
by each wrapped node, by `Monitor.acting(node)` for code outside LangGraph, and by
`MonitoredHandoff.receive` in another thread. An access with no actor, or with an actor that
serves no principal, is recorded in `Monitor.unseen` and not guessed. With `fail_closed=True`
such a read of a labelled value is masked instead of allowed.
"""

from __future__ import annotations

import contextlib
import contextvars
import copy
import dataclasses
import fnmatch
import functools
import inspect
import itertools
import json
import os
import sys
import threading
from collections import defaultdict
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Literal, Protocol

import irspec
import lgtrace
from lgtrace import principal_part

Mode = Literal["block", "flag", "raise"]
MODES: tuple[Mode, ...] = ("block", "flag", "raise")
Label = frozenset[str | None]
INPUT_NODE = "input"
IN_CHANNEL = "in"


# ---------------------------------------------------------------------------------------------
# Records


@dataclass(frozen=True)
class Violation:
  """One disallowed access. `action` says what the monitor did: `masked` (blank or absent),
  `substituted` (the reader's latest visible value), `skipped` (a write), `flagged` or
  `raised`."""
  seam: str
  op: Literal["read", "write"]
  channel: str
  key: str
  agent: str
  writers: tuple[str, ...]
  action: str


@dataclass(frozen=True)
class Unseen:
  """An access the monitor cannot attribute or cannot see, reported rather than guessed."""
  seam: str
  event: str
  channel: str
  key: str = ""
  detail: str = ""


class MonitorViolation(PermissionError):
  """Raised in `raise` mode at a disallowed access."""

  def __init__(self, violation: Violation) -> None:
    super().__init__(f"{violation.agent} may not {violation.op} {violation.channel} "
                     f"[{violation.key}] written by {', '.join(violation.writers)}")
    self.violation = violation


# ---------------------------------------------------------------------------------------------
# Policies


class Policy(Protocol):
  def may_read(self, writer: str, reader: str, channel: str) -> bool: ...

  def may_write(self, writer: str, channel: str) -> bool: ...


def _principal(agent: str) -> str:
  return principal_part(agent) if "@" in agent else ""


@dataclass(frozen=True)
class Isolation:
  """A reader serving `P` reads only values written on `P`'s behalf, except on channels
  matching a `shared` pattern (fnmatch, e.g. `file:skills/*`), or from a `public` principal."""
  shared: tuple[str, ...] = ()
  public: frozenset[str] = frozenset()

  def may_read(self, writer: str, reader: str, channel: str) -> bool:
    wp = _principal(writer)
    return (wp == _principal(reader) or wp in self.public
            or any(fnmatch.fnmatchcase(channel, p) for p in self.shared))

  def may_write(self, writer: str, channel: str) -> bool:
    return True


def board_channel(board: str) -> str:
  """The channel of an `lgtrace` board name `K#P`, `K#P/T` or either with `<-writer`."""
  return board.rpartition("#")[0] or board


@dataclass(frozen=True)
class SpecPolicy:
  """An irspec configuration as a policy. `edges` holds (channel, writer, reader) at `level`,
  where a principal-level edge names principals and an agent-level edge names agents."""
  edges: frozenset[tuple[str, str, str]]
  writes: frozenset[tuple[str, str]]
  level: Literal["principal", "agent"] = "principal"
  own: bool = True

  @classmethod
  def from_spec(cls, spec: irspec.Spec | Mapping[str, Any] | str | os.PathLike[str],
                level: Literal["principal", "agent"] = "principal",
                own: bool | None = None) -> SpecPolicy:
    if isinstance(spec, str | os.PathLike):
      spec = json.loads(Path(spec).read_text())
    if isinstance(spec, Mapping):
      spec = irspec.from_dict(spec)
    lvl = _principal if level == "principal" else (lambda a: a)
    edges = frozenset((board_channel(b), lvl(w), lvl(r)) for b in spec.boards
                      for w in spec.writers_of(b) for r in spec.readers_of(b))
    writes = frozenset((board_channel(b), w) for b in spec.boards for w in spec.writers_of(b))
    return cls(edges, writes, level, level == "principal" if own is None else own)

  def _lvl(self, agent: str) -> str:
    return _principal(agent) if self.level == "principal" else agent

  def may_read(self, writer: str, reader: str, channel: str) -> bool:
    if self.own and _principal(writer) == _principal(reader):
      return True
    ch = IN_CHANNEL if writer.startswith(INPUT_NODE + "@") else channel
    return (ch, self._lvl(writer), self._lvl(reader)) in self.edges

  def may_write(self, writer: str, channel: str) -> bool:
    return self.level == "principal" or (channel, writer) in self.writes


# ---------------------------------------------------------------------------------------------
# Masking


def blank(x: Any) -> Any:
  """The empty value of `x`'s type, as `monitor/langgraph.py`'s `blank` and Lean's `view`
  reading `none`. Nodes index keys directly, so a hidden value is blanked, not removed."""
  match x:
    case bool():
      return False
    case int() | float():
      return type(x)()
    case str() | bytes() | list() | tuple() | dict() | set() | frozenset():
      return type(x)()
    case _:
      return None


def absent(path: str) -> Callable[[Any], Any]:
  """A mask that makes the value absent, for seams that cannot hand back another value."""
  def mask(_value: Any) -> Any:
    raise FileNotFoundError(2, "No such file or directory (masked by lgmonitor)", path)
  return mask


def _snapshot(value: Any) -> Any:
  try:
    return copy.deepcopy(value)
  except Exception:  # noqa: BLE001, an uncopyable value is kept as is
    return value


# ---------------------------------------------------------------------------------------------
# The monitor


@dataclass(frozen=True)
class Actor:
  """Who is acting, a node or external task serving `principal` in run `run`."""
  node: str
  principal: str | None
  run: str | None = None

  @property
  def agent(self) -> str | None:
    return None if self.principal is None else lgtrace.agent_name(self.node, self.principal)


_ACTOR: contextvars.ContextVar[Actor | None] = contextvars.ContextVar("lgmonitor_actor",
                                                                      default=None)
_RUNS = itertools.count(1)
Loc = tuple[str, str]


@dataclass
class Stats:
  reads: int = 0
  writes: int = 0
  unlabelled: int = 0


class Monitor:
  """Labels, the per-location history of writes, and the violation and unseen logs.

  `history[loc][writer]` keeps the latest value each writer put at `loc`, stamped with a global
  sequence number, for seams that substitute. A blocked reader gets the newest entry among the
  writers it may read. The stamp matters, see `Ir/MonitorMask.lean`: per-writer logs alone do
  not fix which of two visible writers wrote last.
  """

  def __init__(self, policy: Policy, mode: Mode = "block", fail_closed: bool = False) -> None:
    if mode not in MODES:
      raise ValueError(f"mode must be one of {MODES}")
    self.policy, self.mode, self.fail_closed = policy, mode, fail_closed
    self.labels: dict[Loc, Label] = {}
    self.history: dict[Loc, dict[str, tuple[int, Any]]] = defaultdict(dict)
    self.violations: list[Violation] = []
    self.unseen: list[Unseen] = []
    self.stats = Stats()
    self.overwrites: set[str] = set()
    """State keys whose channel keeps only the last value, so a write replaces the label."""
    self.lock = threading.RLock()
    self._seq = itertools.count(1)

  # Attribution

  @staticmethod
  def actor() -> Actor | None:
    return _ACTOR.get()

  def agent(self) -> str | None:
    a = _ACTOR.get()
    return a.agent if a else None

  @contextlib.contextmanager
  def as_actor(self, actor: Actor | None) -> Iterator[Actor | None]:
    token = _ACTOR.set(actor)
    try:
      yield actor
    finally:
      _ACTOR.reset(token)

  @contextlib.contextmanager
  def serving(self, principal: str, run: str | None = None) -> Iterator[Actor]:
    """The body serves `principal`, as one run of the app for one user."""
    with self.as_actor(Actor(INPUT_NODE, principal, run or f"run{next(_RUNS)}")) as a:
      yield a  # type: ignore[misc]

  @contextlib.contextmanager
  def acting(self, node: str, principal: str | None = None) -> Iterator[Actor]:
    """The body runs as `node` outside LangGraph, for `principal` or the current actor's."""
    cur = _ACTOR.get()
    actor = Actor(node, principal if principal is not None else cur and cur.principal,
                  cur.run if cur else None)
    with self.as_actor(actor) as a:
      yield a  # type: ignore[misc]

  def label_input(self, thread: str, value: Any) -> None:
    """Label each state key of a run input as written by `input@P` in `thread`."""
    for k, _ in lgtrace._fields(value):  # noqa: SLF001, the shared field reader
      if lgtrace._is_state_key(k):  # noqa: SLF001
        self.write("state", k, thread, None, merge=k not in self.overwrites)

  # Records

  def _record(self, v: Violation) -> Violation:
    with self.lock:
      self.violations.append(v)
    return v

  def report_unseen(self, seam: str, event: str, channel: str, key: str = "",
                    detail: str = "") -> None:
    with self.lock:
      self.unseen.append(Unseen(seam, event, channel, key, detail))

  def label(self, channel: str, key: str) -> Label | None:
    with self.lock:
      return self.labels.get((channel, key))

  # Writes

  def write(self, seam: str, channel: str, key: str, value: Any, *, merge: bool = False,
            keep: bool = False, agent: str | None | Literal[False] = False) -> bool:
    """Label `value` written at (channel, key) by the current agent. Returns whether the write
    may go ahead, which is False only for a write the policy forbids in `block` mode.

    `merge` unions the writer into the label, for appending channels. `keep` stores a copy for
    seams that substitute on a blocked read.
    """
    writer = self.agent() if agent is False else agent
    loc = (channel, key)
    if writer is None:
      self.report_unseen(seam, "write", channel, key, "no principal")
    elif not self.policy.may_write(writer, channel):
      action = {"block": "skipped", "flag": "flagged", "raise": "raised"}[self.mode]
      v = self._record(Violation(seam, "write", channel, key, writer, (writer,), action))
      if self.mode == "raise":
        raise MonitorViolation(v)
      if self.mode == "block":
        return False
    with self.lock:
      self.stats.writes += 1
      old = self.labels.get(loc, frozenset()) if merge else frozenset()
      self.labels[loc] = old | {writer}
      if keep and writer is not None:
        self.history[loc][writer] = (next(self._seq), _snapshot(value))
    return True

  def move(self, src: Loc, dst: Loc) -> None:
    """A rename, as of a temporary file onto its target."""
    with self.lock:
      if src in self.labels:
        self.labels[dst] = self.labels.pop(src)
      if src in self.history:
        self.history[dst] = self.history.pop(src)

  def drop(self, loc: Loc) -> None:
    with self.lock:
      self.labels.pop(loc, None)
      self.history.pop(loc, None)

  # Reads

  def denied(self, label: Label, reader: str, channel: str) -> tuple[str, ...]:
    """The writers in `label` the policy does not allow `reader` to read on `channel`.
    An unattributed writer is denied only when failing closed."""
    return tuple(sorted(
      (w or "?") for w in label
      if (w is None and self.fail_closed)
      or (w is not None and not self.policy.may_read(w, reader, channel))))

  def check(self, seam: str, channel: str, key: str) -> tuple[str | None, tuple[str, ...]]:
    """The reader and the writers it may not read at (channel, key). Records unattributed
    readers and writers and unlabelled reads."""
    label = self.label(channel, key)
    reader = self.agent()
    with self.lock:
      self.stats.reads += 1
      if label is None:
        self.stats.unlabelled += 1
    if label is None:
      return reader, ()
    if None in label:
      self.report_unseen(seam, "read", channel, key, "value has an unattributed writer")
    if reader is None:
      self.report_unseen(seam, "read", channel, key, "no principal")
      return None, (tuple(sorted(w or "?" for w in label)) if self.fail_closed else ())
    return reader, self.denied(label, reader, channel)

  def visible(self, channel: str, key: str, reader: str | None) -> tuple[bool, Any]:
    """The newest kept value at (channel, key) whose writer `reader` may read."""
    with self.lock:
      hist = dict(self.history.get((channel, key), {}))
    seen = [(seq, v) for w, (seq, v) in hist.items()
            if reader is not None and self.policy.may_read(w, reader, channel)]
    return (True, _snapshot(max(seen, key=lambda e: e[0])[1])) if seen else (False, None)

  def read(self, seam: str, channel: str, key: str, value: Any, *,
           mask: Callable[[Any], Any] = blank, substitute: bool = False) -> Any:
    """`value` read at (channel, key) by the current agent, or what the mode makes of it."""
    reader, bad = self.check(seam, channel, key)
    if not bad:
      return value
    return self.violate(seam, channel, key, reader, bad, value, mask, substitute)

  def violate(self, seam: str, channel: str, key: str, reader: str | None,
              bad: tuple[str, ...], value: Any, mask: Callable[[Any], Any] = blank,
              substitute: bool = False) -> Any:
    agent = reader or "?"
    if self.mode == "flag":
      self._record(Violation(seam, "read", channel, key, agent, bad, "flagged"))
      return value
    if self.mode == "raise":
      raise MonitorViolation(self._record(
        Violation(seam, "read", channel, key, agent, bad, "raised")))
    found, alt = self.visible(channel, key, reader) if substitute else (False, None)
    self._record(Violation(seam, "read", channel, key, agent, bad,
                           "substituted" if found else "masked"))
    return alt if found else mask(value)

  # Prompts baked into a graph before the run

  def built(self, channel: str, value: Any) -> None:
    """A graph factory baked `value` into the graph of the current run."""
    a = _ACTOR.get()
    self.write("built", channel, (a.run or "") if a else "", value)

  def read_built(self) -> None:
    """The current node reads every value baked into its run's graph. The value lives in the
    node's closure, so nothing can be masked, and in `block` mode a violation raises."""
    a = _ACTOR.get()
    run = (a.run or "") if a else ""
    with self.lock:
      chans = [c for (c, k) in self.labels if k == run and c.startswith(lgtrace.BUILT_PREFIX)]
    for c in chans:
      reader, bad = self.check("built", c, run)
      if bad:
        if self.mode == "block":
          raise MonitorViolation(self._record(
            Violation("built", "read", c, run, reader or "?", bad, "raised")))
        self.violate("built", c, run, reader, bad, None)

  # Summary

  def summary(self) -> dict[str, Any]:
    with self.lock:
      return {
        "mode": self.mode,
        "violations": [dataclasses.asdict(v) for v in self.violations],
        "unseen": [dataclasses.asdict(u) for u in self.unseen],
        "reads": self.stats.reads, "writes": self.stats.writes,
        "unlabelled_reads": self.stats.unlabelled,
      }


# ---------------------------------------------------------------------------------------------
# Seam: an app's own storage methods


def guarded(fn: Callable[..., Any], monitor: Monitor, mode: lgtrace.Mode,
            channel: Callable[..., str], key: Callable[..., str] = lambda *a, **k: "",
            value: Callable[[tuple[Any, ...], dict[str, Any], Any], Any] | None = None,
            mask: Callable[[Any], Any] = blank, skipped: Any = False) -> Callable[..., Any]:
  """`fn` under the monitor, the enforcing twin of `lgtrace.recorded`.

  A read returns the monitor's verdict on the result, which in `block` mode is the reader's
  latest visible value at the location, else `mask(result)`. A write is labelled, and when the
  policy forbids it in `block` mode it is not performed and returns `skipped`. The written value
  is `value(args, kwargs, None)`, by default the first argument after `self`.
  """
  def written(args: tuple[Any, ...], kwargs: dict[str, Any]) -> Any:
    if value is not None:
      return value(args, kwargs, None)
    return args[1] if len(args) > 1 else None

  def before(args: tuple[Any, ...], kwargs: dict[str, Any]) -> bool:
    return mode == "read" or monitor.write("storage", channel(*args, **kwargs),
                                           key(*args, **kwargs), written(args, kwargs),
                                           keep=True)

  def after(args: tuple[Any, ...], kwargs: dict[str, Any], result: Any) -> Any:
    if mode == "write":
      return result
    return monitor.read("storage", channel(*args, **kwargs), key(*args, **kwargs), result,
                        mask=mask, substitute=True)

  if inspect.iscoroutinefunction(fn):
    @functools.wraps(fn)
    async def awrapper(*args: Any, **kwargs: Any) -> Any:
      if not before(args, kwargs):
        return skipped
      return after(args, kwargs, await fn(*args, **kwargs))
    return awrapper

  @functools.wraps(fn)
  def wrapper(*args: Any, **kwargs: Any) -> Any:
    if not before(args, kwargs):
      return skipped
    return after(args, kwargs, fn(*args, **kwargs))
  return wrapper


# ---------------------------------------------------------------------------------------------
# Seam: thread hand-off


@dataclass
class MonitoredHandoff(lgtrace.Handoff):
  """An `lgtrace.Handoff` that also carries the monitor's actor across the queue.

  `send` labels the queued value with the sender and remembers the sender's actor. `receive`
  opens `node` for the sender's principal in whatever thread runs it and checks the read of the
  queued value. Use `receive_value` to get the value the monitor lets through.
  """
  monitor: Monitor | None = None
  actors: dict[Any, Actor | None] = field(default_factory=dict)

  def send(self, key: Any, value: Any) -> None:
    super().send(key, value)
    assert self.monitor is not None
    self.monitor.write("queue", self.channel, str(key), value, keep=True)
    with self.lock:
      self.actors[key] = _ACTOR.get()

  @contextlib.contextmanager
  def receive_value(self, key: Any, node: str, value: Any) -> Iterator[Any]:
    assert self.monitor is not None
    with self.lock:
      sender = self.actors.get(key)
    if sender is None or sender.principal is None:
      self.monitor.report_unseen("queue", "receive", self.channel, str(key),
                                 "no sender with a principal")
    actor = Actor(node, sender.principal if sender else None, sender.run if sender else None)
    with self.monitor.as_actor(actor), super().receive(key, node, value):
      yield self.monitor.read("queue", self.channel, str(key), value, substitute=True)

  @contextlib.contextmanager
  def receive(self, key: Any, node: str, value: Any) -> Iterator[str]:
    with self.receive_value(key, node, value):
      yield lgtrace.current_task() or ""


# ---------------------------------------------------------------------------------------------
# Seam: files


_MON_FILES: list[MonitoredFiles] = []
_MON_LOCK = threading.Lock()
_MON_GUARD = threading.local()
FILE_EVENTS = frozenset({"open", "os.rename", "os.remove", "os.listdir", "os.scandir",
                         "os.mkdir"})
UNSEEN_EVENTS = frozenset({"subprocess.Popen", "os.system", "os.posix_spawn", "os.exec",
                           "sqlite3.connect", "ctypes.dlopen", "mmap.__new__"})


def _mon_audit(event: str, args: tuple[Any, ...]) -> None:
  if not _MON_FILES or (event not in FILE_EVENTS and event not in UNSEEN_EVENTS):
    return
  if getattr(_MON_GUARD, "busy", False):
    return
  _MON_GUARD.busy = True
  try:
    for rec in list(_MON_FILES):
      rec.on_event(event, args)
  finally:
    _MON_GUARD.busy = False


def _install_mon_hook() -> None:
  with _MON_LOCK:
    if not getattr(sys, "_lgmonitor_audit", False):
      sys.addaudithook(_mon_audit)
      sys._lgmonitor_audit = True  # type: ignore[attr-defined]


def _open_kind(mode: Any, flags: Any) -> tuple[bool, bool, bool]:
  """(reads, writes, appends) of an `open` audit event. A truncating open reads nothing."""
  if isinstance(mode, str):
    w = any(c in mode for c in "wax+")
    reads = "r" in mode or ("+" in mode and "w" not in mode and "x" not in mode)
    return reads, w, w and "w" not in mode and "x" not in mode
  f = flags if isinstance(flags, int) else 0
  acc = f & (os.O_RDONLY | os.O_WRONLY | os.O_RDWR)
  trunc = bool(f & os.O_TRUNC)
  w = acc in (os.O_WRONLY, os.O_RDWR)
  return acc == os.O_RDONLY or (acc == os.O_RDWR and not trunc), w, w and not trunc


class MonitoredFiles:
  """Files under `root` as channels `file:<path below root>`, on CPython audit hooks.

  An open for writing labels the file with the opener at once. A rename moves the label, so an
  atomic save through a temporary file labels its target. A removal drops it. An open for
  reading, and a directory listing (`os.listdir`, `os.scandir`, which `Path.iterdir`, `glob`
  and `os.walk` use), are checked, and in `block` mode a disallowed one raises
  `FileNotFoundError`, as if the file were not there. A listing is checked against the labels
  of the files and directories directly in it, since it shows their names.

  Unseen. `os.stat`, `os.path.exists` and `os.access` raise no audit event, so a file's
  existence, size and time leak past the monitor. Child processes and native code (`sqlite3`,
  `ctypes`, `mmap`) read files without Python's hook, so their events are reported in
  `Monitor.unseen` while the recorder is open.
  """

  def __init__(self, root: str | os.PathLike[str], monitor: Monitor) -> None:
    self.root = os.path.realpath(root)
    self.monitor = monitor
    self._rel = lgtrace.FileRecorder(root).rel

  def __enter__(self) -> MonitoredFiles:
    _install_mon_hook()
    with _MON_LOCK:
      _MON_FILES.append(self)
    return self

  def __exit__(self, *exc: Any) -> None:
    with _MON_LOCK:
      _MON_FILES.remove(self)

  def rel(self, path: Any) -> str | None:
    return self._rel(path)

  @staticmethod
  def channel(rel: str) -> str:
    return lgtrace.FILE_PREFIX + rel

  def _check_read(self, rel: str) -> None:
    ch = self.channel(rel)
    self.monitor.read("file", ch, "", None, mask=absent(os.path.join(self.root, rel)))

  def _check_list(self, rel: str) -> None:
    """A listing shows the names of the files and directories directly in `rel`."""
    parent = "" if rel == "." else rel
    with self.monitor.lock:
      children = [(c, lab) for (c, _), lab in self.monitor.labels.items()
                  if c.startswith(lgtrace.FILE_PREFIX)
                  and os.path.dirname(c.removeprefix(lgtrace.FILE_PREFIX)) == parent]
      self.monitor.stats.reads += 1
    reader = self.monitor.agent()
    ch = self.channel(rel)
    if reader is None:
      if children:
        self.monitor.report_unseen("file", "listdir", ch, "", "no principal")
      return
    bad = tuple(sorted({w for c, lab in children
                        for w in self.monitor.denied(lab, reader, c)}))
    if bad:
      self.monitor.violate("file", ch, "", reader, bad, None,
                           absent(os.path.join(self.root, rel)))

  def on_event(self, event: str, args: tuple[Any, ...]) -> None:
    if event in UNSEEN_EVENTS:
      self.monitor.report_unseen("file", event, "", "", repr(args[:2])[:200])
      return
    if event == "open":
      path, mode, flags = (tuple(args) + (None, None, None))[:3]
      rel = self.rel(path)
      if rel is None or os.path.isdir(os.path.join(self.root, rel)):
        return
      reads, writes, appends = _open_kind(mode, flags)
      if reads and os.path.exists(os.path.join(self.root, rel)):
        self._check_read(rel)
      if writes and not self.monitor.write("file", self.channel(rel), "", None, merge=appends):
        raise PermissionError(13, "Write denied by lgmonitor", path)
    elif event == "os.rename":
      src, dst = self.rel(args[0]), self.rel(args[1])
      if src is not None and dst is not None:
        self.monitor.move((self.channel(src), ""), (self.channel(dst), ""))
      elif dst is not None:
        self.monitor.write("file", self.channel(dst), "", None)
    elif event == "os.remove":
      rel = self.rel(args[0])
      if rel is not None:
        self.monitor.drop((self.channel(rel), ""))
    elif event == "os.mkdir":
      rel = self.rel(args[0])
      if rel is not None and not os.path.exists(os.path.join(self.root, rel)):
        self.monitor.write("file", self.channel(rel), "", None)
    elif event in ("os.listdir", "os.scandir"):
      target = args[0] if args else "."
      rel = self.rel(target if target is not None else ".")
      if rel is not None:
        self._check_list(rel)


# ---------------------------------------------------------------------------------------------
# Seam: the LangGraph store


@functools.cache
def _monitored_store_class() -> type:
  from langgraph.store.base import BaseStore, GetOp, Item, PutOp, SearchOp

  class MonitoredStore(BaseStore):
    """A store that forwards to `inner` and enforces the monitor per (namespace, key). A blocked
    get returns the reader's latest visible item or None, a blocked search drops the item."""

    def __init__(self, inner: BaseStore, monitor: Monitor) -> None:
      self.inner, self.monitor = inner, monitor
      self.supports_ttl = getattr(inner, "supports_ttl", False)
      self.ttl_config = getattr(inner, "ttl_config", None)

    def __getattr__(self, name: str) -> Any:
      return getattr(self.__dict__["inner"], name)

    @staticmethod
    def _ch(ns: Iterable[str]) -> str:
      return lgtrace.store_channel(ns)

    def _pre(self, ops: list[Any]) -> list[Any]:
      kept = []
      for op in ops:
        if isinstance(op, PutOp) and not self.monitor.write(
            "store", self._ch(op.namespace), op.key, op.value, keep=True):
          continue
        kept.append(op)
      return kept

    def _post(self, ops: list[Any], results: list[Any]) -> list[Any]:
      out = []
      for op, res in zip(ops, results, strict=True):
        match op:
          case GetOp() if res is not None:
            got = self.monitor.read("store", self._ch(op.namespace), op.key, res,
                                    mask=lambda _v: None, substitute=True)
            out.append(got if got is None or got is res else
                       Item(value=got, key=res.key, namespace=res.namespace,
                            created_at=res.created_at, updated_at=res.updated_at))
          case SearchOp():
            items = []
            for it in res or []:
              got = self.monitor.read("store", self._ch(it.namespace), it.key, it,
                                      mask=lambda _v: None)
              if got is not None:
                items.append(got)
            out.append(items)
          case _:
            out.append(res)
      return out

    def _run(self, ops: list[Any], kept: list[Any], results: list[Any]) -> list[Any]:
      by_op = dict(zip(map(id, kept), results, strict=True))
      return self._post(ops, [by_op.get(id(op)) for op in ops])

    def batch(self, ops: Iterable[Any]) -> list[Any]:
      ops = list(ops)
      kept = self._pre(ops)
      return self._run(ops, kept, self.inner.batch(kept))

    async def abatch(self, ops: Iterable[Any]) -> list[Any]:
      ops = list(ops)
      kept = self._pre(ops)
      return self._run(ops, kept, await self.inner.abatch(kept))

  return MonitoredStore


def monitored_store(monitor: Monitor, inner: Any = None) -> Any:
  """A `MonitoredStore` around `inner`, a fresh `InMemoryStore` by default."""
  if inner is None:
    from langgraph.store.memory import InMemoryStore
    inner = InMemoryStore()
  return _monitored_store_class()(inner, monitor)


# ---------------------------------------------------------------------------------------------
# Seam: state keys


@dataclass
class _Session:
  """Duck-types `lgtrace._Session` for `TrackedDict` and `TrackedObject`. A read of a key in
  `bad` is a violation, recorded once per key and call."""
  monitor: Monitor
  thread: str
  reader: str | None
  bad: dict[str, tuple[str, ...]]
  live: bool = True
  done: set[str] = field(default_factory=set)

  def record(self, key: str, value: Any) -> None:
    if not self.live or key in self.done:
      return
    self.done.add(key)
    with self.monitor.lock:
      self.monitor.stats.reads += 1
      if self.monitor.labels.get((key, self.thread)) is None:
        self.monitor.stats.unlabelled += 1
    if key in self.bad:
      # In `block` mode the value is already blank. This records the read, or raises.
      self.monitor.violate("state", key, self.thread, self.reader, self.bad[key], value,
                           mask=lambda v: v)


def _state_keys(state: Any) -> list[tuple[str, Any]]:
  if isinstance(state, Mapping):
    return list(state.items())
  names = lgtrace._field_names(state)  # noqa: SLF001
  return [(n, getattr(state, n)) for n in names]


def _masked_copy(state: Any, masked: Mapping[str, Any]) -> Any:
  if not masked:
    return state
  if isinstance(state, Mapping):
    return {**state, **masked}
  if callable(getattr(state, "model_copy", None)):
    return state.model_copy(update=dict(masked))
  if dataclasses.is_dataclass(state) and not isinstance(state, type):
    return dataclasses.replace(state, **masked)
  return state


def state_view(monitor: Monitor, state: Any, thread: str,
               node: str) -> tuple[Any, _Session | None]:
  """The state as the current agent may read it, behind a proxy that reports reads."""
  reader = monitor.agent()
  pairs = _state_keys(state)
  if not pairs and not isinstance(state, Mapping):
    monitor.report_unseen("state", "untracked", node, thread, type(state).__name__)
    return state, None
  if reader is None:
    monitor.report_unseen("state", "read", node, thread, "no principal")
  bad: dict[str, tuple[str, ...]] = {}
  for k, _ in pairs:
    lab = monitor.label(k, thread)
    if lab is not None and reader is not None:
      d = monitor.denied(lab, reader, k)
      if d:
        bad[k] = d
  masked = {k: blank(v) for k, v in pairs if k in bad} if monitor.mode == "block" else {}
  session = _Session(monitor, thread, reader, bad)
  view = _masked_copy(state, masked)
  proxy = lgtrace.tracking_proxy(view, session)  # type: ignore[arg-type]
  return (proxy if proxy is not None else view), session


def _updates(out: Any) -> list[tuple[str, Any]]:
  """The (key, value) writes of a node's return value."""
  from langgraph.types import Command, Send
  match out:
    case Command():
      upd = out.update
      return [] if upd is None else _updates(upd)
    case list() | tuple() if all(isinstance(x, Command | Send | Mapping) for x in out):
      return [kv for x in out for kv in _updates(x)]
    case Send():
      return []
    case _:
      return [(k, v) for k, v in lgtrace._fields(out)  # noqa: SLF001
              if lgtrace._is_state_key(k)]  # noqa: SLF001


def _thread_of(config: Any) -> str:
  conf = (config or {}).get("configurable", {}) if isinstance(config, Mapping) else {}
  return str(conf.get("thread_id", ""))


@functools.cache
def _monitored_runnable_class() -> type:
  from langchain_core.runnables import Runnable

  class MonitoredRunnable(Runnable):
    """Node or routing code under the monitor. It runs as actor `node` for the current
    principal, reads a masked state, and labels the keys it returns."""

    def __init__(self, inner: Any, node: str, monitor: Monitor, route: bool,
                 built: bool) -> None:
      self.inner, self.node, self.monitor = inner, node, monitor
      self.route, self.built = route, built
      self.name = getattr(inner, "name", None)

    def _open(self, state: Any, config: Any) -> tuple[Any, Any, _Session | None, str]:
      cur = _ACTOR.get()
      if cur is None:
        self.monitor.report_unseen("state", "node", self.node, "", "no principal")
      actor = Actor(self.node, cur.principal if cur else None, cur.run if cur else None)
      token = _ACTOR.set(actor)
      thread = _thread_of(config)
      if self.built:
        self.monitor.read_built()
      view, session = state_view(self.monitor, state, thread, self.node)
      return token, view, session, thread

    def _close(self, out: Any, view: Any, state: Any, session: _Session | None,
               thread: str, agent: str | None) -> Any:
      if session is not None:
        session.live = False
      if out is view:
        return state  # a pass-through writes nothing new
      if not self.route:
        for k, _ in _updates(out):
          self.monitor.write("state", k, thread, None, merge=k not in self.monitor.overwrites,
                             agent=agent)
      return out

    def invoke(self, input: Any, config: Any = None, **kwargs: Any) -> Any:
      token, view, session, thread = self._open(input, config)
      agent = self.monitor.agent()
      try:
        out = self.inner.invoke(view, config, **kwargs)
      finally:
        _ACTOR.reset(token)
      return self._close(out, view, input, session, thread, agent)

    async def ainvoke(self, input: Any, config: Any = None, **kwargs: Any) -> Any:
      token, view, session, thread = self._open(input, config)
      agent = self.monitor.agent()
      try:
        out = await self.inner.ainvoke(view, config, **kwargs)
      finally:
        _ACTOR.reset(token)
      return self._close(out, view, input, session, thread, agent)

  return MonitoredRunnable


def _wrap(runnable: Any, node: str, monitor: Monitor, route: bool,
          built_readers: frozenset[str]) -> Any:
  from langgraph.pregel import Pregel
  cls = _monitored_runnable_class()
  if isinstance(runnable, cls):
    return runnable
  if isinstance(runnable, Pregel) and hasattr(runnable, "builder"):
    return monitor_compiled(runnable, monitor, built_readers, prefix=f"{node}/")
  return cls(runnable, node, monitor, route, node in built_readers and not route)


LAST_VALUE = frozenset({"LastValue", "LastValueAfterFinish", "AnyValue", "EphemeralValue",
                        "UntrackedValue"})


def monitor_graph(builder: Any, monitor: Monitor,
                  built_readers: Iterable[str] = (), prefix: str = "") -> Any:
  """A copy of `StateGraph` `builder` whose nodes and routing functions run under `monitor`.
  A routing function is part of its source node. `built_readers` names the nodes that read
  the prompts a factory baked into the graph, such as `create_agent`'s `model`."""
  readers = frozenset(built_readers)
  monitor.overwrites |= {k for k, c in getattr(builder, "channels", {}).items()
                         if type(c).__name__ in LAST_VALUE}
  new = copy.copy(builder)
  new.nodes = {k: lgtrace._replace(  # noqa: SLF001
                 spec, runnable=_wrap(spec.runnable, prefix + k, monitor, False, readers))
               for k, spec in builder.nodes.items()}
  new.branches = defaultdict(dict, {
    src: {name: lgtrace._replace(  # noqa: SLF001
            b, path=_wrap(b.path, prefix + src, monitor, True, readers))
          for name, b in bs.items()}
    for src, bs in builder.branches.items()})
  return new


def monitor_compiled(graph: Any, monitor: Monitor, built_readers: Iterable[str] = (),
                     prefix: str = "", **overrides: Any) -> Any:
  """A compiled graph recompiled from its builder under `monitor`, as
  `lgtrace.instrument_compiled` does, with its compile settings except `overrides`."""
  builder = monitor_graph(graph.builder, monitor, built_readers, prefix)
  return recompile_builder(graph, builder, **overrides)


def recompile_builder(graph: Any, builder: Any = None, **overrides: Any) -> Any:
  """`builder` (by default `graph.builder`) compiled with `graph`'s settings and `overrides`.
  With no builder given this is the unmonitored baseline of `monitor_compiled`."""
  builder = graph.builder if builder is None else builder
  accepted = inspect.signature(builder.compile).parameters
  settings = {arg: getattr(graph, attr) for arg, attr in lgtrace.COMPILE_ATTRS.items()
              if arg in accepted and hasattr(graph, attr)}
  return builder.compile(**{**settings, **overrides})
