# A checker for cross-user leaks in LangGraph applications

A checker that a LangGraph application keeps its users apart. It runs the application with a
marker-copying fake LLM, lifts the runs into a protocol configuration, reports every agent of a
victim that an attacker can reach, and exports a certificate that Lean checks.

## Case studies

### Prerequisites

- Python 3.12 and [uv](https://docs.astral.sh/uv/getting-started/installation/)
- [Git](https://git-scm.com/downloads)
- [Docker](https://docs.docker.com/get-started/get-docker/)

### Running individual case studies


Set the case study files

```sh
./setup-case-studies.sh               # Every case study
./setup-case-studies.sh deerflow yuxi # Selected case studies
```

Run the case study

```sh
./run-case-study.sh deerflow
```

The applications pin different versions of the same packages, such as LangGraph, so
each case study gets its own venv in `case-studies/venvs/`, built from its
`case-studies/requirements/<name>.txt`. The clones go in `case-studies/apps/`. Both are
gitignored, and the scripts below make and use them, so you never call a venv yourself.

| Case study | Name | In the paper |
|---|---|---|
| DeerFlow | `deerflow` | Q1, leak and fix (#2627) |
| Yuxi | `yuxi` | Q1, leak and fix (#594) |
| aegra | `aegra` | Q1, leak and fix (#275, #276) |
| aegra, thread ownership | `aegra_threads` | Q1, leak and fix (#336, #337), needs Docker |
| Aix-DB | `aix_db` | Q2, false positive |
| open_deep_research | `open_deep_research` | Q2, no known bug |
| agent-service-toolkit | `agent_service_toolkit` | Q2, sharing by design |
| executive-ai-assistant | `executive_ai_assistant` | Q2, new finding |
| kaymen99 email automation | `kaymen99` | Q2, the clear gap |
| agents-from-scratch | `agents_from_scratch` | Q2, tutorial |


### DeerFlow

This runs four versions of DeerFlow, each in its own process, and prints the findings of each.

- `00a90bb` shares one memory file across users.
- `2e05f38` (#2153) crashes every memory update.
- `da174dfd` (#2566) leaves the memory updater on the shared file.
- `c0da2782` (#2627) completes the fix.

The specs land in `specs/`. Check from `proofs` the certificate that no agent of user B is
reachable from user A in the fixed version.

```sh
lake env lean Ir/Generated/DeerflowFixed.lean
```

The same export of `deerflow.json` or `deerflow-da174dfd.json` fails to check.

`./run-case-study.sh aegra_threads` starts the Postgres container it needs and stops it
afterwards.

`python -m lgauto <repo>` runs a LangGraph application with no driver.

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

## Checker

Run the unit tests from `checker`. The tests of a case study skip themselves when its clone or
venv is missing.

```sh
cd checker
python3 -m unittest discover -s tests
```
