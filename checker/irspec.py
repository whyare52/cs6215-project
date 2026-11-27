"""IR spec for multi-agent testbeds, mirroring `Ir.Config` and `Ir.Adversary` in Lean.

`reach` is the same flow relation as `Ir.Reach`. It is unverified, and `lean_export` turns its
answer into a certificate that Lean checks with `Ir.closed_sound`.

A board in JSON is either a list of members, each of whom reads and writes it, or an object
`{"readers": [...], "writers": [...]}`, where a missing key means nobody. `Spec.boards` keeps
every agent on a board in either role, and `readers` and `writers` refine it. A board missing
from `readers` or `writers` falls back to `boards`, so a spec built from member lists alone
means what it always did.
"""

from __future__ import annotations

import json
from collections import deque
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Spec:
  agents: tuple[str, ...]
  boards: Mapping[str, frozenset[str]]
  owner: Mapping[str, str]
  sees: Mapping[str, frozenset[str]]
  echo_sees: frozenset[str]
  controls: frozenset[str]
  injects: frozenset[str] = frozenset()
  readers: Mapping[str, frozenset[str]] = field(default_factory=dict)
  writers: Mapping[str, frozenset[str]] = field(default_factory=dict)

  @property
  def vars(self) -> tuple[str, ...]:
    return tuple(self.owner)

  def readers_of(self, board: str) -> frozenset[str]:
    return self.readers.get(board, self.boards[board])

  def writers_of(self, board: str) -> frozenset[str]:
    return self.writers.get(board, self.boards[board])

  def boards_of(self, agent: str) -> tuple[str, ...]:
    """Boards the agent is on, reading or writing."""
    return tuple(b for b, members in self.boards.items() if agent in members)

  def writes_to(self, agent: str) -> tuple[str, ...]:
    return tuple(b for b in self.boards if agent in self.writers_of(b))

  def validate(self) -> Spec:
    known = set(self.agents)
    problems = [
      *(f"board {b} has unknown member {a}"
        for b, ms in self.boards.items() for a in ms if a not in known),
      *(f"{role} names unknown board {b}"
        for role, m in (("readers", self.readers), ("writers", self.writers))
        for b in m if b not in self.boards),
      *(f"{role} of board {b} include {a}, who is not on it"
        for role, m in (("readers", self.readers), ("writers", self.writers))
        for b, ms in m.items() if b in self.boards for a in ms - self.boards[b]),
      *(f"variable {v} has unknown owner {a}" for v, a in self.owner.items() if a not in known),
      *(f"sees names unknown agent {a}" for a in self.sees if a not in known),
      *(f"sees names unknown variable {v}"
        for vs in self.sees.values() for v in vs if v not in self.owner),
      *(f"echo_sees names unknown variable {v}" for v in self.echo_sees if v not in self.owner),
      *(f"adversary controls unknown agent {a}" for a in self.controls if a not in known),
      *(f"adversary injects unknown board {b}" for b in self.injects if b not in self.boards),
    ]
    if problems:
      raise ValueError("; ".join(problems))
    return self


def _var_set(value: Any, agent: str | None, owner: Mapping[str, str]) -> frozenset[str]:
  match value:
    case "all":
      return frozenset(owner)
    case "own" if agent is not None:
      return frozenset(v for v, a in owner.items() if a == agent)
    case "none":
      return frozenset()
    case list():
      return frozenset(value)
    case _:
      raise ValueError(f"cannot read variable set {value!r}")


def _roles(value: Any) -> tuple[frozenset[str], frozenset[str]]:
  """Readers and writers of one board, from a member list or a readers/writers object."""
  match value:
    case Mapping():
      unknown = set(value) - {"readers", "writers"}
      if unknown:
        raise ValueError(f"board roles have unknown keys {sorted(unknown)}")
      return frozenset(value.get("readers", [])), frozenset(value.get("writers", []))
    case list() | tuple() | set() | frozenset():
      return frozenset(value), frozenset(value)
    case _:
      raise ValueError(f"cannot read board {value!r}")


def from_dict(data: Mapping[str, Any]) -> Spec:
  agents = tuple(data["agents"])
  owner = dict(data["owner"])
  raw_sees = data.get("sees", "all")
  sees = (
    {a: _var_set(raw_sees.get(a, "none"), a, owner) for a in agents}
    if isinstance(raw_sees, Mapping)
    else {a: _var_set(raw_sees, a, owner) for a in agents}
  )
  adversary = data.get("adversary", {})
  roles = {b: _roles(v) for b, v in data["boards"].items()}
  return Spec(
    agents=agents,
    boards={b: r | w for b, (r, w) in roles.items()},
    readers={b: r for b, (r, _) in roles.items()},
    writers={b: w for b, (_, w) in roles.items()},
    owner=owner,
    sees=sees,
    echo_sees=_var_set(data.get("echo_sees", "all"), None, owner),
    controls=frozenset(adversary.get("controls", [])),
    injects=frozenset(adversary.get("injects", [])),
  ).validate()


def load(path: str | Path) -> Spec:
  return from_dict(json.loads(Path(path).read_text()))


def _edges(spec: Spec, x: str) -> Iterable[tuple[str, str]]:
  """Agents one flow step from reachable agent `x`, each with the rule that reaches it."""
  for b in spec.writes_to(x):
    for y in spec.readers_of(b):
      yield y, f"board {b}"
  for v in (v for v, a in spec.owner.items() if a == x):
    for y in spec.agents:
      if v in spec.sees.get(y, frozenset()):
        yield y, f"sees {v}"
    if v in spec.echo_sees:
      owners = frozenset(spec.owner.values())
      for b in spec.boards:
        if spec.writers_of(b) & owners:
          for y in spec.readers_of(b):
            yield y, f"echo {v} on {b}"


def explain(spec: Spec) -> dict[str, list[str]]:
  """Breadth-first reachability. Maps each reachable agent to a shortest flow path."""
  start = {a: [f"controlled {a}"] for a in spec.controls}
  for b in spec.injects:
    for y in spec.readers_of(b):
      start.setdefault(y, [f"SYS injects {b}"])
  paths = dict(start)
  queue = deque(paths)
  while queue:
    x = queue.popleft()
    for y, rule in _edges(spec, x):
      if y not in paths:
        paths[y] = [*paths[x], f"{x} -> {y} via {rule}"]
        queue.append(y)
  return paths


def reach(spec: Spec) -> frozenset[str]:
  return frozenset(explain(spec))


def holders(spec: Spec, secret_holders: Iterable[str]) -> Spec:
  """The same testbed with the secret holders as the only sources, as in `Ir.holders`."""
  return replace(spec, controls=frozenset(secret_holders), injects=frozenset())


def leaks(spec: Spec, secret_holders: Iterable[str]) -> frozenset[str]:
  """Adversary agents that a secret holder's data can reach."""
  return reach(holders(spec, secret_holders)) & spec.controls
