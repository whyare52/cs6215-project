# A checker for cross-user leaks in LangGraph applications

A checker that a LangGraph application keeps its users apart. It runs the application with a
marker-copying fake LLM, lifts the runs into a protocol configuration, reports every agent of a
victim that an attacker can reach, and exports a certificate that Lean checks.

## Prerequisites

- [Git](https://git-scm.com/downloads)
- Python 3.12 or later and [uv](https://docs.astral.sh/uv/getting-started/installation/)
- [Lean 4](https://lean-lang.org/install/) through `elan`, which provides `lake`. The version
  is pinned in `proofs/lean-toolchain` and `lake` downloads it on first use.
- [Docker](https://docs.docker.com/get-started/get-docker/), only for the `aegra_threads` case
  study and the two unit tests that need Postgres

Every command below starts from the root of this repository. Do the steps in order, since the
unit tests and the certificate checks need the proofs built.

## 1. Build the proofs

```sh
cd proofs
lake build
```

It ends with `Build completed successfully`.

## 2. Run the unit tests

```sh
cd checker
uv sync
uv run python -m unittest discover -s tests
```

`uv sync` makes `checker/.venv`. Do not use the system `python3`, which has no LangGraph and
makes most tests skip themselves.

The tests of a case study skip themselves when its clone or venv is missing, so the number of
skips depends on step 3. Before step 3 the run ends with `OK (skipped=30)` or so. After every
case study is set up it ends with

```
Ran 186 tests in ...
OK (skipped=2)
```

where the two skipped tests need a Postgres server.

## 3. Run the case studies

```sh
./setup-case-studies.sh               # Every case study
./setup-case-studies.sh deerflow yuxi # Or selected ones
./run-case-study.sh deerflow
```

`run-case-study.sh` sets its case study up first if needed, so the first line is optional.
Setting up every case study clones ten applications and builds a venv for each, which takes
tens of minutes and several gigabytes.

The applications pin different versions of the same packages, such as LangGraph, so
each case study gets its own venv in `case-studies/venvs/`, built from its
`case-studies/requirements/<name>.txt`. The clones go in `case-studies/apps/`. Both are
gitignored, and the scripts make and use them, so you never call a venv yourself.

Each run prints one line per version, `== <version>: <n> scripts, <m> findings`, and the
findings with their paths. The expected numbers of findings are

| Case study | Name | Findings per version | In the paper |
|---|---|---|---|
| DeerFlow | `deerflow` | 7, crash, 1, 0 | RQ1, leak and fix (#2153, #2627) |
| Yuxi | `yuxi` | 2, 0 | RQ1, leak and fix (#594) |
| aegra | `aegra` | 2, 0 | RQ1, leak and fix (#275, #276) |
| aegra, thread ownership | `aegra_threads` | 1, 0 | RQ1, leak and fix (#336, #337), needs Docker |
| Aix-DB | `aix_db` | 0, 4, 0 | RQ2, false positive |
| open_deep_research | `open_deep_research` | 0 | RQ2, no findings |
| agent-service-toolkit | `agent_service_toolkit` | 3, 3, 3, 0, 3 | RQ2, sharing by design |
| executive-ai-assistant | `executive_ai_assistant` | 21 | RQ2, new finding |
| kaymen99 email automation | `kaymen99` | 3, 4 | RQ2 |
| agents-from-scratch | `agents_from_scratch` | 3 | RQ2 |

Some runs print `app crash in ...` lines. These are bugs of the applications themselves on
some scripts, not failures of the checker, and they are expected for `deerflow` (the version
`2e05f38`), `executive_ai_assistant` and `kaymen99`.

`./run-case-study.sh aegra_threads` starts the Postgres container it needs and stops it
afterwards.

### DeerFlow

This runs four versions of DeerFlow, each in its own process, and prints the findings of each.

- `00a90bb` shares one memory file across users.
- `2e05f38` (#2153) crashes every memory update.
- `da174dfd` (#2566) leaves the memory updater on the shared file.
- `c0da2782` (#2627) completes the fix.

The specs land in `specs/`.

## 4. Check a certificate in Lean

Lean accepts the claim that no agent of user B is reachable from user A in the fixed version
of DeerFlow. The command prints nothing and exits with 0.

```sh
cd proofs
lake env lean Ir/Generated/DeerflowFixed.lean
```

Lean rejects the same claim for the original version. This needs the specs that
`./run-case-study.sh deerflow` writes.

```sh
cd checker
uv run python lean_export.py --claim-principal B ../specs/deerflow.json /tmp/claim.lean
cd ../proofs
lake env lean /tmp/claim.lean
```

The last command fails with ``Tactic `decide` proved that the proposition ... is false``.
With `../specs/deerflow-fixed.json` in place of `../specs/deerflow.json` it passes.

## Running without a driver

`python -m lgauto <repo>`, from `checker` and under `uv run`, runs a LangGraph application with
no driver.

## Proofs

Open it in [VS Code](https://code.visualstudio.com/) with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

| Result | File | Lean name |
|---|---|---|
| Protocols, `Reach` (the taint analysis) | `Ir/Basic.lean` | `Config`, `run`, `Reach` |
| Noninterference | `Ir/Noninterference.lean` | `noninterference`, `assign_fixed` |
| Confidentiality | `Ir/Confidentiality.lean` | `confidentiality`, `no_leak` |
| Exactness | `Ir/Completeness.lean` | `reach_iff_influence` |
| Certificates | `Ir/Check.lean` | `Closed`, `closed_sound` |
| Owner first | `Ir/Ordering.lean` | `run_assign` |
| Monotonicity | `Ir/Monotone.lean` | `Reach.mono` |
| Clear gap | `Ir/ClearGap.lean` | `bug_weaker`, `fix_reaches_writeB` |
| Ordered noninterference | `Ir/OrderedReach.lean` | `reachSum_sound`, `reachSum_reach` |
| Clear gap closed | `Ir/ClearGapClosed.lean` | `fix_clears_writeB`, `fix_safe_sessions` |
| Every schedule | `Ir/OrderedClosed.lean` | `closedB`, `every_schedule_sound` |
| Refinement | `Ir/Refinement.lean` | `Host.refine`, `Host.assign_fixed` |
| Supersteps | `Ir/Superstep.lean` | `runPar_eq`, `assign_fixed_par` |
| Trusted humans | `Ir/TrustedHumans.lean` | `noninterference_trusting`, `reach_trusting_iff_influence` |
