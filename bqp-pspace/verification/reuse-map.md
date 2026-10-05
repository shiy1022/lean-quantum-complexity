# Reuse map (S00)

Baseline: repository commit `fb7f202` (plan commit; BQP sources unchanged since `da6aba9`).
Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. All paths are under
`bqp-pp/src/`, consumed read-only through the `Baseline` library in `bqp-pspace/lakefile.toml`.

Status column: **proved** = no `sorry` in the file and the declaration is used by an audited
endpoint; **stub** = statement-only reference file (contains `sorry`, must not be used).

| Declaration | Source | Exact type (abridged) | Status | Planned use |
|---|---|---|---|---|
| `ShiBQP.bqp_subset_pp` | `BQP-final-inclusion.lean` | `ShiBQP.BQP ⊆ ShiClassPP.PP` | proved, audited in baseline | S15 composition |
| `ShiClassPP.PP`, `countAccept` | `Definitions/Def_ShiClassPP.lean` | `countAccept R x m = (univ.filter fun b : Fin m → Bool => R (x, List.ofFn b) = true).card` | definition | S06, S15 |
| `PvsNP.PolyTimeChecker`, `encodePair` | `Definitions/Def_PvsNP.lean` | `Nonempty (TM2ComputableInPolyTime encodePair encodeBool R)`; `encodePair (x,y) = x.map inl ++ y.map inr` | definition | S04, S10 |
| `ShiTMSubroutine.stmt`, `cfg`, `run` | `AMPUNI-subroutine-lift.lean` | `run M c = c.bind (step M)` (= `flip bind tm.step`, the `EvalsTo` iterator, by `rfl`) | proved | S01 reachability, S10 lifting |
| `ShiTMSubroutine.stepAux_lift` | same | `stepAux (stmt f q) v S = cfg f (stepAux q v S)` | proved | S10 |
| `ShiTMSubroutine.run_to_terminal` | same | relabelled run up to a terminal label with handoff | proved | S10 halt redirection |
| `ShiTMSubroutine.run_lift`, `run_iter_lift` | `AMPUNI-subroutine-full-lift.lean` | exact relabelling of whole runs | proved | S10 |
| `ShiTMStackGrowth.size` | `AMPUNI-run-stack-growth.lean` | `size S = ∑ k, (S k).length` | definition | S01 `cfgSpace` |
| `ShiTMStackGrowth.potential_run_le`, `run_size_le` | same | per-step growth `C` ⇒ `size` after `n` steps ≤ initial + `n*C` | proved | S04 |
| `ShiTMStackGrowth.pushBudget`, `stepAux_size_le`, `finite_growth` | `AMPUNI-finite-stack-growth.lean` | every finite-label machine has a uniform per-step growth constant | proved | S03, S04 |
| `ShiTMTotalFunction.halted_unique`, `outputs_unique` | `AMPUNI-total-function.lean` | uniqueness of halted configurations / outputs | proved | S02, S04 (post-halt) |
| `ShiTM.initList_haltList_laws` | `Theorems/Thm_ShiTM_initList_haltList_laws.lean` | init/halt stack laws | **stub (`sorry`)** | not used; re-proved in `Space/Model.lean` |

Checks for a pre-existing corrected space interface: no `PSPACE`, `SpaceBounded` or
`cfgSpace` declaration exists in `bqp-pp/src` (searched 2026-10-05); the historical
`Def_ShiClassPSPACE` is not in this repository and is not used.

Model notes recorded for later tasks:

- `FinTM2`'s finiteness fields are not global instances; `Space/Model.lean` exposes
  `tm.kFin`, `tm.ΛFin`, `tm.σFin` as instances (`ShiSpace.finTM2_kFin`, …). Baseline files use
  definitionally equal local instances.
- `Fintype (tm.Γ k)` is available only for `k = k₀`; S03 must not assume it elsewhere.
