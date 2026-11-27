"""Subject adapters for `lgtrace`, one module per LangGraph app, plus shared helpers.

Each adapter module exposes `subject()` (and `fixed_subject()` where a fix exists) and a `main()`
that prints findings and writes the spec to `project/specs/`. Run them from `project/checker`
with the subject's own venv, as in the project README.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import os
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

PY_DIR = Path(__file__).resolve().parents[1]
PROJECT_DIR = PY_DIR.parent
APPS_DIR = Path(os.environ.get("LGTRACE_APPS", PROJECT_DIR / "case-studies" / "apps"))
SPECS_DIR = PROJECT_DIR / "specs"
VENVS_DIR = PROJECT_DIR / "case-studies" / "venvs"

if str(PY_DIR) not in sys.path:
  sys.path.insert(0, str(PY_DIR))

import irspec  # noqa: E402
import lgtrace  # noqa: E402


def run_order(principals: Sequence[str], attackers: frozenset[str]) -> tuple[str, ...]:
  """The users in the order every subject runs them, the same for all subjects.

  The attacker goes first and last, with every other user in between, so the victims run after
  the attacker has left state behind and the attacker's last run shows its own state still
  reaches it.
  """
  attacker = next(p for p in principals if p in attackers)
  others = tuple(p for p in principals if p not in attackers)
  return (attacker, *others, attacker)


def turns(order: Sequence[str]) -> tuple[tuple[str, int], ...]:
  """Each run of `order` with the number of earlier runs by the same user."""
  return tuple((p, order[:i].count(p)) for i, p in enumerate(order))


def repo(name: str) -> Path:
  """The checkout of subject repo `name`, which must exist."""
  path = APPS_DIR / name
  if not path.is_dir():
    raise FileNotFoundError(f"subject repo missing: {path} (run setup-case-studies.sh)")
  return path


def on_path(path: Path) -> None:
  if str(path) not in sys.path:
    sys.path.insert(0, str(path))


ORDERED_ENV = "LGTRACE_ORDERED"


def ordered_path(name: str) -> Path:
  return SPECS_DIR / f"{name}.ordered.json"


def report(name: str, subject: lgtrace.Subject, write: bool = True) -> dict[str, Any]:
  """Trace `subject`, print its findings with their paths, write its spec, return a summary.

  With `LGTRACE_ORDERED=1` in the environment it also writes the ordered analysis input
  (`lgtrace.ordered_dict`) to `specs/<name>.ordered.json`, whether or not the spec is written,
  so `--no-write` leaves the spec alone and still exports the order and summaries.
  """
  trace = lgtrace.trace_subject(subject)
  data = lgtrace.spec_dict(trace, subject.attackers)
  found = lgtrace.findings(irspec.from_dict(data))
  out = SPECS_DIR / f"{name}.json"
  SPECS_DIR.mkdir(parents=True, exist_ok=True)
  if write:
    out.write_text(json.dumps(data, indent=2) + "\n")
  if os.environ.get(ORDERED_ENV) == "1":
    ordered_path(name).write_text(
      json.dumps(lgtrace.ordered_dict(trace, subject.attackers), indent=1) + "\n")
  summary = {
    "name": name,
    "scripts": len(subject.scripts),
    "findings": found,
    "flows": sorted(map(list, lgtrace.flows(trace))),
    "cross_reads": sorted(map(list, lgtrace.cross_reads(trace))),
    "shared_reads": sorted(map(list, lgtrace.shared_reads(trace))),
    "unexplained": sorted(map(list, lgtrace.unexplained(trace, subject.attackers))),
    "fallbacks": sorted(trace.fallbacks),
    "unattributed": trace.unattributed,
    "spec": str(out) if write else None,
  }
  print_summary(summary)
  return summary


def matches(script: Mapping[str, Any], where: Mapping[str, str]) -> bool:
  """Whether every `key=value` holds, where a dict choice matches any of its values."""
  def hit(v: Any, want: str) -> bool:
    return str(v) == want or isinstance(v, Mapping) and any(str(x) == want for x in v.values())
  return all(k in script and hit(script[k], v) for k, v in where.items())


@dataclasses.dataclass(frozen=True)
class Options:
  where: Mapping[str, str]
  write: bool

  def narrow(self, subject: lgtrace.Subject) -> lgtrace.Subject:
    """`subject` with only the scripts matching `where`."""
    kept = tuple(s for s in subject.scripts if matches(s, self.where))
    if not kept:
      raise SystemExit(f"no script matches {dict(self.where)}")
    return dataclasses.replace(subject, scripts=kept)


def options(argv: Sequence[str] | None = None) -> Options:
  """`--where key=value` (repeatable) keeps matching scripts. `--no-write` skips the spec file,
  which a filtered run always does."""
  ap = argparse.ArgumentParser()
  ap.add_argument("--where", action="append", default=[], metavar="KEY=VALUE")
  ap.add_argument("--no-write", action="store_true")
  args = ap.parse_args(argv)
  where = dict(w.split("=", 1) for w in args.where)
  return Options(where, not (args.no_write or where))


def print_summary(summary: Mapping[str, Any]) -> None:
  print(f"== {summary['name']}: {summary['scripts']} scripts, "
        f"{len(summary['findings'])} findings, spec {summary['spec'] or 'not written'}")
  for victim, path in summary["findings"].items():
    print(f"finding {victim}")
    print("".join(f"  {step}\n" for step in path), end="")
  for src, channel, reader in summary["flows"]:
    print(f"flow {src} -> {channel} -> {reader}")
  for src, channel, reader in summary["unexplained"]:
    print(f"unexplained flow {src} -> {channel} -> {reader}, a recorder missed its path")
  for src, channel, reader, writer in summary["cross_reads"]:
    print(f"non-marker read {src} -> {channel} -> {reader} (last written by {writer})")
  if summary["fallbacks"]:
    print(f"reads not tracked, whole input used: {', '.join(summary['fallbacks'])}")
  if summary["unattributed"]:
    print(f"unattributed store ops and reads: {summary['unattributed']}")


def emit_json(summaries: list[dict[str, Any]]) -> None:
  """One machine-readable line for the tests, after the human-readable report."""
  print("LGTRACE_JSON " + json.dumps(summaries))
