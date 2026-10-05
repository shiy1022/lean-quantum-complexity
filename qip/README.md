# QIP = QIP(3) (in progress)

Lean 4 development toward `ShiQIP.qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3` for explicitly
defined H/S/T/X/CNOT, polynomial-time-uniform quantum interactive verifiers, following
[the execution plan](../plans/QIP_THREE_MESSAGE_PLAN.md) and its
[task manifest](../plans/QIP_THREE_MESSAGE_TASKS.json).

**Status: foundations only. The endpoint theorem does not exist yet.** See
[verification/progress.md](verification/progress.md) for each task's status and evidence.

## Layout

- `src/Quantum/` — generic finite-dimensional mathematics (registers, reindexing).
- `src/QIP/` — protocol syntax, encoding, scalar arithmetic; later the protocol theory.
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
is **not** Sherlock clean-build evidence.
