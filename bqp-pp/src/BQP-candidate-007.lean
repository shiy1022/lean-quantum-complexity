import Definitions.Def_ShiClassRel
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count

namespace BQPReferenceValidation.Source7

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ASM-CONSb: the RESHAPED `BRIDGE-SEMb` core, cut ALPHABET-GENERIC (gotcha 214).

`BRIDGE-SEMb` carried a `C`/`D` split that gotcha 271 retires.  What is left, once `D` and the
`C d ≤ D d` bound are deleted, is a statement about a finite branch set `io`, a phase exponent
`kk`, an endpoint map `Y` and an accepting predicate -- no `Instr`, no `Bits`, no `runLayered`.
This file proves that residue:

* (A) THE FIBRE PARTITION.  Summing the WITHIN-FIBRE ordered pair counts `P y d` over the
  ACCEPTING endpoints gives exactly the global count `C d` of ordered pairs that land on a
  COMMON accepting endpoint at phase difference `d`.  This is the step that turns `RING-1`'s
  per-output identity into one global `ℤ[√2]` element.
* (B) THE CONSUMER IDENTITY.  The acceptance sum -- written in `acceptProb`'s own shape
  `∑ y, if accepting then ‖amp y‖² else 0` -- equals `(1/2)^h ((C₀ - C₄) + √2 (C₁ - C₃))`.

`RING-1` conjunct (2) (per fibre) and `COUNT-1` conjunct (0) enter as hypotheses, as does the
path-sum factorisation of the amplitude. -/

theorem _root_.BQPReferenceValidation.candidate7 :
    ∀ (Om io : Type) [Fintype Om] [DecidableEq Om] [Fintype io] [DecidableEq io]
      (acc : Om → Bool) (h : ℕ) (kk : io → ℕ) (Y : io → Om) (amp : Om → ℂ) (om : ℂ)
      (P : Om → ℕ → ℕ) (C : ℕ → ℕ),
      -- the within-fibre ordered pair counts, graded by phase difference mod 8
      (∀ (y : Om) (d : ℕ), P y d = (Finset.univ.filter
          (fun q : io × io => Y q.1 = y ∧ Y q.2 = y
            ∧ (kk q.1 + 8 - kk q.2 % 8) % 8 = d)).card) →
      -- the global count: a COMMON endpoint, which must be accepting
      (∀ d : ℕ, C d = (Finset.univ.filter
          (fun q : io × io => acc (Y q.1) = true ∧ Y q.1 = Y q.2
            ∧ (kk q.1 + 8 - kk q.2 % 8) % 8 = d)).card) →
      -- COUNT-1 conjunct (0): the path-sum prefactor contributes exactly `(1/2)^h`
      (∀ (n : ℕ) (z : ℂ),
          ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ n * z‖ ^ 2 = (1 / 2 : ℝ) ^ n * ‖z‖ ^ 2) →
      -- the path sum, fibred over the output string
      (∀ y : Om, amp y = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h
          * ∑ i ∈ Finset.univ.filter (fun i : io => Y i = y), om ^ kk i) →
      -- RING-1 conjunct (2), applied fibrewise
      (∀ y : Om, ‖∑ i ∈ Finset.univ.filter (fun i : io => Y i = y), om ^ kk i‖ ^ 2
          = ((P y 0 : ℝ) - (P y 4 : ℝ))
            + Real.sqrt 2 * ((P y 1 : ℝ) - (P y 3 : ℝ))) →
      -- (A) THE FIBRE PARTITION
      (∀ d : ℕ, ∑ y ∈ Finset.univ.filter (fun y : Om => acc y = true), P y d = C d)
      -- (B) THE CONSUMER IDENTITY, in `acceptProb`'s own shape
      ∧ (∑ y : Om, (if acc y = true then ‖amp y‖ ^ 2 else 0))
          = (1 / 2 : ℝ) ^ h * (((C 0 : ℝ) - (C 4 : ℝ))
              + Real.sqrt 2 * ((C 1 : ℝ) - (C 3 : ℝ))) := by
  intro Om io _ _ _ _ acc h kk Y amp om P C hP hC hpref hamp hring
  have hpart : ∀ d : ℕ,
      ∑ y ∈ Finset.univ.filter (fun y : Om => acc y = true), P y d = C d := by
    intro d
    have hH : ∀ q ∈ Finset.univ.filter
        (fun q : io × io => acc (Y q.1) = true ∧ Y q.1 = Y q.2
          ∧ (kk q.1 + 8 - kk q.2 % 8) % 8 = d),
        Y q.1 ∈ Finset.univ.filter (fun y : Om => acc y = true) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact hq.1
    rw [hC d, Finset.card_eq_sum_card_fiberwise hH]
    refine Finset.sum_congr rfl ?_
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [hP y d]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨?_, ?_, h3⟩, h1⟩
      · rw [h1]; exact hy
      · rw [h1, h2]
    · rintro ⟨⟨_, h2, h3⟩, h4⟩
      refine ⟨h4, ?_, h3⟩
      rw [← h2]; exact h4
  refine ⟨hpart, ?_⟩
  have hsum : ∀ d : ℕ,
      ∑ y ∈ Finset.univ.filter (fun y : Om => acc y = true), (P y d : ℝ) = (C d : ℝ) := by
    intro d
    rw [← hpart d]
    push_cast
    ring
  have hstep : ∀ y ∈ Finset.univ.filter (fun y : Om => acc y = true),
      ‖amp y‖ ^ 2 = (1 / 2 : ℝ) ^ h * (((P y 0 : ℝ) - (P y 4 : ℝ))
        + Real.sqrt 2 * ((P y 1 : ℝ) - (P y 3 : ℝ))) := by
    intro y _
    rw [hamp y, hpref, hring y]
  rw [← Finset.sum_filter, Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hsum 0, hsum 1, hsum 3, hsum 4]

end BQPReferenceValidation.Source7

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate7
    let target ← getConstInfo ``ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate7
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count; axioms {axioms}"
