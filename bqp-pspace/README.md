# PP ⊆ PSPACE and BQP ⊆ PSPACE (in progress)

**Status: work in progress. Neither containment is proved yet.** See
[`../plans/BQP_PSPACE_PLAN.md`](../plans/BQP_PSPACE_PLAN.md) and
[`verification/progress.md`](verification/progress.md).

The target class is the corrected finite-multistack `ShiSpace.PSPACE`
([`src/Space/Model.lean`](src/Space/Model.lean)): a total `Turing.TM2Computable` decider whose
every reachable configuration has total stack length at most a `Polynomial ℕ` in the input
length. No time bound is imposed.

## Build (local)

The `Baseline` library compiles `../bqp-pp/src` read-only into this project's `.lake`;
Mathlib packages are shared with `../bqp-pp/.lake/packages`.

```bash
cd ../bqp-pp && lake exe cache get   # once: pinned Mathlib cache
cd ../bqp-pspace
LEAN_NUM_THREADS=5 lake build Baseline ShiSpace
python scripts/audit.py              # build + fresh-import axiom audits
```

On Windows, set `git config core.autocrlf false` in this repository before checkout (source
hashes are of LF files) and run Python with `PYTHONUTF8=1`.
