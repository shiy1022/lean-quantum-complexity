# QIP = QIP(3)

Lean 4 development toward `ShiQIP.qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3` for explicitly
defined H/S/T/X/CNOT, polynomial-time-uniform quantum interactive verifiers, following
[the execution plan](../plans/QIP_THREE_MESSAGE_PLAN.md) and its
[task manifest](../plans/QIP_THREE_MESSAGE_TASKS.json).

**Status: proved.** `ShiQIP.qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3` (`src/QIP/ThreeMessage.lean`)
depends only on `propext`, `Classical.choice` and `Quot.sound`, with no `sorry`. Evidence: a
from-scratch **local** build and audit (not Sherlock), recorded in
[verification/clean-build.json](verification/clean-build.json) and
[verification/axioms.json](verification/axioms.json); the definitions are reviewed in
[verification/definition-review.md](verification/definition-review.md). See
[verification/progress.md](verification/progress.md) for each task's status and evidence.

## Layout

- `src/Quantum/` — generic finite-dimensional mathematics (registers, reindexing).
- `src/QIP/` — protocol syntax and semantics, the transformations, the class equality.
- `src/QIP/Uniform/` — concrete TM2 machines and the polynomial-time printer.
- `src/QIP/Audit/` — fresh-import audit files: exact `#check` types and `#print axioms`.
- `scripts/manifest.py` — source manifest (`--check` also re-verifies bqp-pp and bqp-pspace).
- `scripts/audit.py` — `--self-test` and `--source-only` never invoke Lean; the default run
  builds `ShiQIP` with one Lean thread and audits every axiom report.
- `verification/` — baseline, reuse map, Mathlib inventory, progress ledger, audit results.

The project reuses the pinned dependency checkout of `bqp-pp` (`packagesDir`) and builds a
read-only selection of `bqp-pp/src` as the `Baseline` library.

## Checking

```bash
python scripts/manifest.py --check
```

```bash
python scripts/audit.py --source-only
```

```bash
python scripts/audit.py
```

The last command compiles. The plan asks for compilation on Sherlock inside a Slurm
allocation (`python scripts/audit.py --require-slurm`). Evidence currently recorded comes from
a local Windows workstation with one Lean thread, by the user's instruction of 2026-10-05; it
is **not** Sherlock clean-build evidence. `python scripts/clean_build.py` (refuses to run if
`.lake/build` exists) rebuilds every project object from scratch and writes
`verification/clean-build.json`; by the user's instruction of 2026-10-07 it was run locally in
place of the Sherlock build.
