"""Ordered taint analysis with flow summaries, mirroring `Ir.reachSum` and `Ir.closedB`.

The input is the JSON of `lgtrace.ordered_dict`: a spec, a flow summary per agent, the traced
order of turns per script and the concrete marker flows. Three analyses run on it.
- `traced(..., summaries=False)`, `reachSum` with the black-box summary on each traced schedule.
  It differs from `Reach` by order alone.
- `traced(...)`, `reachSum` with the exported summaries on each traced schedule.
- `closure(...)`, the least taint state above the initial one that every turn keeps inside
  itself. By `Ir.closedB_sound` it bounds `reachSum` on every schedule, so its verdicts do not
  depend on the traced order. With black-box summaries it is `Reach` (`Ir.reach_iff_exists`).

The schedule of a script starts with one turn of every input agent, since inputs never read and
their boards are never replaced. Then each cluster of tasks whose accesses overlap in time runs
as one turn per task when it holds one task, with the turn's kills. A cluster of several tasks
runs with no kills, repeated until the taint state stops growing, which covers every order and
interleaving of its tasks. The last pass, which changes nothing, is left out.

Specs from `lgtrace` have no variables, and a spec with variables is rejected, so `sees`,
`owner` and echoes play no part. `lean_export.to_lean_ordered` states the same results in Lean.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import irspec

INPUT_PREFIX = "input@"


@dataclass(frozen=True)
class Taint:
  boards: frozenset[str] = frozenset()
  agents: frozenset[str] = frozenset()

  def join(self, other: Taint) -> Taint:
    return Taint(self.boards | other.boards, self.agents | other.agents)


@dataclass(frozen=True)
class Turn:
  agent: str
  kills: frozenset[str] = frozenset()


@dataclass(frozen=True)
class Model:
  """A spec with no variables and a flow summary. `dep` holds the outputs whose dependencies
  are narrower than every input, as (agent, output board) to input boards. Every other output
  of every agent may depend on every input."""
  spec: irspec.Spec
  dep: Mapping[tuple[str, str], frozenset[str]] = field(default_factory=dict)

  def reads(self, x: str) -> frozenset[str]:
    return frozenset(b for b in self.spec.boards if x in self.spec.readers_of(b))

  def in_tainted(self, t: Taint, x: str, o: str) -> bool:
    """`Ir.inT`. Some input of output `o` is readable by `x` and tainted."""
    deps = self.dep.get((x, o))
    return any(i in t.boards for i in self.reads(x) if deps is None or i in deps)

  def agent_turn(self, x: str, t: Taint, kills: Iterable[str] = ()) -> Taint:
    """`Ir.agentT` without variables."""
    controlled = x in self.spec.controls
    killed = frozenset(kills)
    boards = {b for b in t.boards if x not in self.spec.writers_of(b)}
    boards |= {b for b in self.spec.writes_to(x)
               if controlled or self.in_tainted(t, x, b) or (b in t.boards and b not in killed)}
    hit = controlled or any(self.in_tainted(t, x, o) for o in self.spec.boards)
    return Taint(frozenset(boards), t.agents | ({x} if hit else frozenset()))

  def sys_turn(self, t: Taint) -> Taint:
    return Taint(t.boards | self.spec.injects, t.agents)

  def init(self) -> Taint:
    return Taint(frozenset(), self.spec.controls)


def model(data: Mapping[str, Any], summaries: bool = True) -> Model:
  spec = irspec.from_dict(data["spec"])
  if spec.vars:
    raise ValueError("the ordered analysis takes specs without variables")
  if not summaries:
    return Model(spec)
  return Model(spec, {(x, o): frozenset(ins)
                      for x, s in data["summaries"].items()
                      for o, ins in s.get("dep", {}).items()})


@dataclass(frozen=True)
class Walk:
  """One schedule as run. `turns` is the expanded schedule, `taint` the final state and
  `cause` the first turn index and board that tainted each agent."""
  script: str
  turns: tuple[Turn, ...]
  taint: Taint
  cause: Mapping[str, tuple[int, str | None]]


def _step(m: Model, turn: Turn, t: Taint, n: int, cause: dict[str, tuple[int, str | None]]
          ) -> Taint:
  after = m.agent_turn(turn.agent, t, turn.kills)
  for a in after.agents - t.agents:
    hot = sorted(i for i in m.reads(a) if i in t.boards)
    cause[a] = (n, hot[0] if hot else None)
  return after


def walk(m: Model, schedule: Mapping[str, Any], kills: bool = True) -> Walk:
  """`Ir.taintAfter` from `Ir.Taint.init` on one exported schedule, clusters expanded."""
  t, n = m.init(), 0
  turns: list[Turn] = []
  cause: dict[str, tuple[int, str | None]] = {a: (-1, None) for a in t.agents}
  if m.spec.injects:
    raise ValueError("the ordered analysis takes specs without injections")
  for a in (a for a in m.spec.agents if a.startswith(INPUT_PREFIX)):
    turns.append(Turn(a))
    t = _step(m, turns[-1], t, n, cause)
    n += 1
  clusters: dict[int, list[Mapping[str, Any]]] = {}
  for turn in schedule["turns"]:
    clusters.setdefault(turn["cluster"], []).append(turn)
  for _, group in sorted(clusters.items()):
    if len(group) == 1:
      turns.append(Turn(group[0]["agent"],
                        frozenset(group[0]["kills"]) if kills else frozenset()))
      t = _step(m, turns[-1], t, n, cause)
      n += 1
      continue
    passes = 0
    while True:
      before, passes = t, passes + 1
      for turn in group:
        turns.append(Turn(turn["agent"]))
        t = _step(m, turns[-1], t, n, cause)
        n += 1
      if t == before:
        break
    if passes > 1:
      del turns[-len(group):]
      n -= len(group)
  return Walk(schedule["script"], tuple(turns), t, cause)


def traced(data: Mapping[str, Any], summaries: bool = True) -> list[Walk]:
  """Every script's schedule, with the exported summaries and kills or the black box."""
  m = model(data, summaries)
  return [walk(m, s, kills=summaries) for s in data["schedules"]]


def closure(data: Mapping[str, Any], summaries: bool = True) -> Taint:
  """The least taint state above the initial one that every turn keeps inside itself."""
  m = model(data, summaries)
  t = m.sys_turn(m.init())
  while True:
    after = t
    for x in m.spec.agents:
      after = after.join(m.agent_turn(x, after))
    if after == t:
      return t
    t = after


def victims(spec: irspec.Spec, agents: Iterable[str]) -> list[str]:
  """Tainted agents of principals the adversary does not control, as `lgtrace.findings`."""
  bad = {a.rpartition("@")[2] for a in spec.controls}
  return sorted(a for a in agents
                if not a.startswith(INPUT_PREFIX) and a.rpartition("@")[2] not in bad)


def attackers(spec: irspec.Spec) -> frozenset[str]:
  return frozenset(a.rpartition("@")[2] for a in spec.controls)


def missed(data: Mapping[str, Any], walks: Sequence[Walk], every: Taint | None = None
           ) -> list[list[str]]:
  """Concrete attacker marker reads whose reader the analysis leaves untainted, which would be
  a soundness bug. With `every`, the closure, else each flow's own script."""
  spec = irspec.from_dict(data["spec"])
  bad = attackers(spec)
  by_script = {w.script: w.taint for w in walks}
  return [f for f in data["flows"] if f[0] in bad and f[2] not in
          (every.agents if every is not None else by_script[f[3]].agents)]


def report(data: Mapping[str, Any]) -> dict[str, Any]:
  """Findings under `Reach`, order alone, summaries on the traced order and summaries on every
  order, with the drops and any missed concrete flow."""
  spec = irspec.from_dict(data["spec"])
  reach = victims(spec, irspec.reach(spec))
  order = traced(data, summaries=False)
  summed = traced(data)
  every = closure(data)
  def union(ws: Sequence[Walk]) -> list[str]:
    return victims(spec, set().union(*(w.taint.agents for w in ws)) if ws else ())
  result = {
    "reach": reach,
    "order": union(order),
    "summary": union(summed),
    "every": victims(spec, every.agents),
    "closure_blackbox": victims(spec, closure(data, summaries=False).agents),
    "missed": {"order": missed(data, order), "summary": missed(data, summed),
               "every": missed(data, summed, every)},
    "kinds": {k: sum(1 for s in data["summaries"].values() if s["kind"] == k)
              for k in ("code", "llm", "opaque", "input")},
    "refined": sum(len(s.get("dep", {})) for s in data["summaries"].values()),
    "kills": sum(len(t["kills"]) for s in data["schedules"] for t in s["turns"]),
    "turns": [len(w.turns) for w in summed],
  }
  result["dropped"] = {k: sorted(set(reach) - set(result[k]))
                       for k in ("order", "summary", "every")}
  return result


def main() -> None:
  ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
  ap.add_argument("ordered", type=Path, nargs="+", help="files written by lgtrace.ordered_dict")
  args = ap.parse_args()
  for path in args.ordered:
    print(json.dumps({"file": path.name, **report(json.loads(path.read_text()))}, indent=1))


if __name__ == "__main__":
  main()
