# PP ⊆ PSPACE progress ledger

Evidence kind: **local check** = `python scripts/audit.py` on the Windows workstation
(Lean 4.33.1, pinned Mathlib `0df444a3` cache, `lake build ShiSpace`, fresh-import axiom
audits) plus `python scripts/manifest.py --check`. Per the user's 2026-10-05 instruction,
compilation runs locally rather than on Sherlock; **no row below is Sherlock clean-build
evidence**. Status vocabulary: not started / in progress / verified (locally) / blocked.

All axiom reports are within `{propext, Classical.choice, Quot.sound}`; no `sorry`, `admit`,
`axiom` or `proof_wanted` occurs in `src/` (checked by `audit.py`). Source hashes are in
`source-manifest.json` and `verification/local-audit.json`.

| Task | Status | Implementation | Evidence | Notes |
|---|---|---|---|---|
| S00 | verified (locally) | `verification/reuse-map.md`, `lakefile.toml`, `scripts/` | baseline graph builds as the `Baseline` Lake library (306 modules); audit self-test | baseline sources read-only, unchanged |
| S01 | verified (locally) | `Space/Model.lean` | `Audit/Space.lean`: 9 reports; exact unfolding of `PolySpaceDecider` | `TM2Computable` + `Polynomial ℕ`, no time bound |
| S02 | verified (locally) | `Space/Run.lean`, `Frame.lean`, `PeakComposition.lean` | `Audit/Run.lean`: 18 reports | all-prefix principle; `Seg` max-composition and common-bound iteration |
| S03 | verified (locally) | `Space/ReachableAlphabet.lean` | `Audit/Alphabet.lean`: 10 reports | finite reachable alphabets without `Fintype (tm.Γ j)`; transient peak ≤ boundary + `pushBudget` |
| S04 | verified (locally) | `Space/TimeToSpace.lean` | `Audit/TimeToSpace.lean`: 5 reports | space ≤ input + D·time on every reachable configuration; corollary `P ⊆ PSPACE` |
| S05 | verified (locally) | `Count/FixedBits.lean` | `Audit/Counting.lean` | little-endian `val`/`word`/`inc`; widths 0, 1, 2 examples |
| S06 | verified (locally) | `Count/Enumeration.lean` | `Audit/Counting.lean` (12 reports with S05) | `prefixCount R x m (2^m) = countAccept R x m`; counter fits m+1 bits |
| S07 | verified (locally) | `Machine/Increment.lean` | `Audit/Machines.lean` | exact run, overflow exit, constant space |
| S08 | verified (locally) | `Machine/Host.lean`, `Loop.lean`, `Regs.lean` | `Audit/Machines.lean`, `Audit/Final.lean` | one generic pop-and-push loop: exact result, peak = max(entry, exit) |
| S09 | verified (locally) | `Machine/EnumInit.lean` | `Audit/Final.lean` | unary `n^k` by k hard-coded rounds; peak ≤ 3(n+1) + 3(n+1)^k |
| S10 | verified (locally) | `Machine/CheckerCall.lean`, `EnumLoop.lean` | `Audit/Machines.lean`, `Audit/Final.lean` | structural embedding, halt redirection, exact restart state (`haltList_pop`) |
| S11 | verified (locally) | `Machine/MajorityTest.lean` | `Audit/Machines.lean` | finite-state scan; ties rejected; m = 0 handled |
| S12 | verified (locally) | `PPToPSPACE.lean` (`head`, `head_step`, `head_upto`) | `Audit/Final.lean` | loop-head invariant `wit = word m j`, `cnt = word (m+1) (prefixCount … j)` |
| S13 | verified (locally) | `Machine/Enumerator.lean`, `EnumFinal.lean`, `PPToPSPACE.lean` (`full_run`, `decider`) | `Audit/Final.lean` | the concrete `FinTM2` halts with `haltList [ppχ R k x]` |
| S14 | verified (locally) | `PPToPSPACE.lean` (`bound`, `boundPoly`) | `Audit/Final.lean` | every reachable configuration ≤ 4(n+1) + 4(n+1)^k + T(n+n^k)·D; same machine as S13 |
| S15 | verified (locally) | `PPToPSPACE.lean`, `BQPToPSPACE.lean` | `Audit/Final.lean`: 26 reports | `ShiSpace.pp_subset_pspace`, `ShiBQP.bqp_subset_pspace` (composes the published endpoint) |
| S16 | verified (locally) | `scripts/audit.py`, `scripts/manifest.py`, `verification/` | 102 axiom reports; manifest check with negative fixture; clean local rebuild (`verification/local-clean-build.json`) | **Sherlock clean build not performed** (local-only per user instruction) |

Remaining, outside this task list: a Sherlock source-matched clean build if cluster evidence
is wanted; any equivalence between the corrected finite-multistack class and a separately
defined single-tape/read-only-input PSPACE (not claimed).
