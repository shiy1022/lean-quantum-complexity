# PP ⊆ PSPACE and BQP ⊆ PSPACE

```lean
theorem ShiSpace.pp_subset_pspace : ShiClassPP.PP ⊆ ShiSpace.PSPACE
theorem ShiBQP.bqp_subset_pspace : ShiBQP.BQP ⊆ ShiSpace.PSPACE
```

[PP ⊆ PSPACE](src/PPToPSPACE.lean) · [BQP ⊆ PSPACE](src/BQPToPSPACE.lean) ·
[Final audit](src/Audit/Final.lean) · [Progress ledger](verification/progress.md) ·
[Plan](../plans/BQP_PSPACE_PLAN.md)

**Verification status: checked locally on a Windows workstation** (Lean 4.33.1, pinned
Mathlib `0df444a3`). Both endpoints, and all 102 audited declarations, depend only on
`propext`, `Classical.choice` and `Quot.sound`. No Sherlock clean build has been run for this
project.

## The space model

`ShiSpace.PSPACE` ([`src/Space/Model.lean`](src/Space/Model.lean)) is a **corrected
finite-multistack class**, not the historical `Def_ShiClassPSPACE`. A language is in it when it
is decided by a total `Turing.TM2Computable` machine such that every configuration reachable
from the initial one has total stack length at most `p(n)`, for a `Polynomial ℕ` `p`. This
includes the input and output stacks and the halted configuration. No time bound is imposed.
Reachable stack alphabets are finite ([`Space/ReachableAlphabet.lean`](src/Space/ReachableAlphabet.lean)),
so stack length measures information up to a machine constant. No equivalence with a
single-tape or read-only-input PSPACE is claimed. As a sanity check, `PvsNP.P ⊆ ShiSpace.PSPACE` is proved.

BQP, PP and the BQP ⊆ PP proof are the published ones in [`../bqp-pp`](../bqp-pp), imported
read-only and unchanged.

## The construction

For a PP language with checker `R` (a `TM2ComputableInPolyTime` certificate `c`) and exponent
`k`, `ShiPPPSPACE.machine c.tm c.inputAlphabet c.outputAlphabet k` is a concrete `FinTM2`. Its
stacks are the checker's stacks plus seven Boolean registers. Its finite control is the
checker's control plus wrapper labels that depend only on `k`.

1. **Init.** Compute `m = n^k` in unary by `k` hard-coded multiplication rounds, and set the
   witness `wit = 0^m` and the counter `cnt = 0^(m+1)`.
2. **Loop.** For each witness `w`:
   - write `encodePair (x, w)` onto the checker input stack, restoring `wit` and the input;
   - run the embedded checker, whose halt is redirected;
   - pop its answer, which leaves all checker stacks empty;
   - increment `cnt` on acceptance, then increment `wit` (ripple carry).
3. **Exit and answer.** Overflow of `wit` ends the loop. A finite-state scan of `cnt` then
   outputs `2 * cnt > 2^m`.

Correctness uses `prefixCount R x m (2^m) = ShiClassPP.countAccept R x m`. The space bound is
`4(n+1) + 4(n+1)^k + T(n+n^k)·D` on every reachable configuration, where `T` is the checker's
time polynomial and `D` its per-step growth constant. This is a maximum over phases, not a sum
over the `2^m` iterations.

## Build and check (local)

The `Baseline` library compiles `../bqp-pp/src` into this project's `.lake`, using the 306
roots of `../bqp-pp/source-manifest.json`. Mathlib packages are shared with
`../bqp-pp/.lake/packages`.

```bash
cd ../bqp-pp && lake exe cache get
cd ../bqp-pspace
LEAN_NUM_THREADS=5 lake build Baseline ShiSpace
python scripts/audit.py              # build + fresh-import axiom audits -> verification/local-audit.json
python scripts/audit.py --self-test  # parser rejects missing/forbidden/duplicate reports
python scripts/manifest.py --check   # source hashes, imports, baseline hashes
```

These commands were run on Windows 10 with Python 3.12 from uv. Set
`git config core.autocrlf false` before checkout, because hashes are of LF files, and run Python
with `PYTHONUTF8=1`. A clean local rebuild of `Baseline` plus `ShiSpace` is recorded in
`verification/local-clean-build.json`.
