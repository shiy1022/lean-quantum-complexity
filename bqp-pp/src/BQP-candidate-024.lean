import Definitions.Def_ShiClassPP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiClassPP_majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings

namespace BQPReferenceValidation.Source24
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! SHORT-COUNT.  THE THREE SHORT INPUTS OF A `PP` MEMBERSHIP, AND THE COUNTING ARITHMETIC
AT WITNESS LENGTHS `0` AND `1`.

`ShiClassPP.PP` HARD-CODES the witness length as `x.length ^ k`.  For `|x| ≤ 1` that length
collapses: `[]` gets `0 ^ k = 0` (whenever `k ≥ 1`) and `[false]`, `[true]` get `1 ^ k = 1`.
No choice of `k` changes this, so any reduction whose counting bound only holds for long
inputs must settle those three strings -- and only those three -- by hand.

* **(1)-(2) THE COUNT AT `m = 0` AND `m = 1`.**  At `m = 0` there is exactly ONE witness,
  the empty string, so `countAccept ∈ {0, 1}`; at `m = 1` there are exactly TWO.  These are
  genuinely different arithmetic cases, which is why `[]` cannot be folded in with the
  length-one strings.
* **(3)-(4) THE MAJORITY CONDITION** `2 * countAccept > 2 ^ m` at those two lengths, in
  terms of the checker's values: at `m = 0` it is just `R (x, [])`, at `m = 1` it demands
  BOTH witnesses accept.
* **(5) A CHECKER CONSTANT IN THE WITNESS** decides the majority condition at EVERY `m`:
  `2 * countAccept > 2 ^ m ↔ c = true`.  This is the arithmetic a hard-coded branch needs.
* **(6)-(7) TOP-LEVEL GLUE.**  A checker that is correct on all inputs of length `≥ 2`, and
  correct in the above sense on `[]`, `[false]`, `[true]`, puts `L` in `PP`.  (7) is the
  form a constant-patched checker delivers.

HONEST LIMITATIONS.
1. **`PolyTimeChecker R` is a HYPOTHESIS in (6) and (7), passed straight through.**  Nothing
   here shows that a patched checker stays poly-time -- that is a separate obligation.
2. Nothing quantum appears; `R` is an arbitrary Boolean checker.
3. `k ≥ 1` is required in (6) and (7): at `k = 0` every input gets witness length
   `x.length ^ 0 = 1`, including `[]`, and the `[]` case below would be the `m = 1`
   arithmetic instead.  That case is not covered here.
-/

open PvsNP ShiClassPP

/-! ### The count at witness lengths `0` and `1` -/

private lemma ca0 (R : Str × Str → Bool) (x : Str) :
    countAccept R x 0 = if R (x, []) = true then 1 else 0 := by
  simp only [countAccept, Finset.card_filter, Finset.univ_unique, Finset.sum_singleton,
    List.ofFn_zero]

private lemma sumFin1 (f : (Fin 1 → Bool) → ℕ) :
    ∑ b : Fin 1 → Bool, f b = f (fun _ => true) + f (fun _ => false) := by
  have hfun : ∀ a : Bool, (fun _ : Fin 1 => a) = (Equiv.funUnique (Fin 1) Bool).symm a := by
    intro a
    funext i
    rfl
  have h := Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool).symm
      (fun a : Bool => f (fun _ => a)) f (fun a => by rw [hfun a])
  rw [← h, Fintype.sum_bool]

private lemma ca1 (R : Str × Str → Bool) (x : Str) :
    countAccept R x 1
      = (if R (x, [true]) = true then 1 else 0) + (if R (x, [false]) = true then 1 else 0) := by
  simp only [countAccept, Finset.card_filter]
  rw [sumFin1]
  simp [List.ofFn_succ]

private lemma maj0 (R : Str × Str → Bool) (x : Str) :
    (2 * countAccept R x 0 > 2 ^ 0 ↔ R (x, []) = true) := by
  rw [ca0]
  by_cases h : R (x, []) = true
  · simp [h]
  · simp [h]

private lemma maj1 (R : Str × Str → Bool) (x : Str) :
    (2 * countAccept R x 1 > 2 ^ 1 ↔ (R (x, [false]) = true ∧ R (x, [true]) = true)) := by
  rw [ca1]
  by_cases h0 : R (x, [false]) = true <;> by_cases h1 : R (x, [true]) = true <;>
    simp [h0, h1]

/-! ### A checker constant in the witness -/

private lemma caConst (R : Str × Str → Bool) (x : Str) (c : Bool) (m : ℕ)
    (hc : ∀ w : Str, R (x, w) = c) :
    countAccept R x m = if c = true then 2 ^ m else 0 := by
  have h : countAccept R x m = ∑ _b : Fin m → Bool, (if c = true then 1 else 0) := by
    simp only [countAccept, Finset.card_filter]
    exact Finset.sum_congr rfl (fun b _ => by simp only [hc])
  have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
  rw [h, Finset.sum_const, Finset.card_univ, hcard]
  cases c <;> simp

private lemma majConst (R : Str × Str → Bool) (x : Str) (c : Bool) (m : ℕ)
    (hc : ∀ w : Str, R (x, w) = c) :
    (2 * countAccept R x m > 2 ^ m ↔ c = true) := by
  rw [caConst R x c m hc]
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
  cases c with
  | true =>
      have hlt : 2 ^ m < 2 * 2 ^ m := by
        rw [two_mul]
        exact Nat.lt_add_of_pos_right h1
      simpa using hlt
  | false => simp

/-! ### Top-level glue -/

private lemma glue (L : Language Bool) (R : Str × Str → Bool) (k : ℕ) (hk : 1 ≤ k)
    (hPT : PolyTimeChecker R)
    (hlong : ∀ x : Str, 2 ≤ x.length →
      (x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k)))
    (hnil : ([] ∈ L ↔ R ([], []) = true))
    (hf : ([false] ∈ L ↔ (R ([false], [false]) = true ∧ R ([false], [true]) = true)))
    (ht : ([true] ∈ L ↔ (R ([true], [false]) = true ∧ R ([true], [true]) = true))) :
    L ∈ PP := by
  refine ⟨R, k, hPT, ?_⟩
  intro x
  rcases x with _ | ⟨a, x'⟩
  · have hm : ([] : Str).length ^ k = 0 := by
      simp only [List.length_nil]
      exact Nat.zero_pow (by omega)
    rw [hm, maj0]
    exact hnil
  · rcases x' with _ | ⟨b, t⟩
    · have hm : ([a] : Str).length ^ k = 1 := by simp
      rw [hm, maj1]
      cases a
      · exact hf
      · exact ht
    · exact hlong (a :: b :: t) (by simp only [List.length_cons]; omega)

theorem _root_.BQPReferenceValidation.candidate24 :
    -- (1) at witness length `0` there is exactly ONE witness, the empty one.
    (∀ (R : Str × Str → Bool) (x : Str),
        countAccept R x 0 = if R (x, []) = true then 1 else 0)
    -- (2) at witness length `1` there are exactly TWO.
  ∧ (∀ (R : Str × Str → Bool) (x : Str),
        countAccept R x 1
          = (if R (x, [true]) = true then 1 else 0)
            + (if R (x, [false]) = true then 1 else 0))
    -- (3) the `PP` majority condition at `m = 0`.
  ∧ (∀ (R : Str × Str → Bool) (x : Str),
        (2 * countAccept R x 0 > 2 ^ 0 ↔ R (x, []) = true))
    -- (4) the `PP` majority condition at `m = 1` -- BOTH witnesses must accept.
  ∧ (∀ (R : Str × Str → Bool) (x : Str),
        (2 * countAccept R x 1 > 2 ^ 1
          ↔ (R (x, [false]) = true ∧ R (x, [true]) = true)))
    -- (5) a checker constant in the witness decides the majority condition at EVERY `m`.
  ∧ (∀ (R : Str × Str → Bool) (x : Str) (c : Bool) (m : ℕ), (∀ w : Str, R (x, w) = c) →
        (2 * countAccept R x m > 2 ^ m ↔ c = true))
    -- (6) TOP-LEVEL GLUE: correctness on inputs of length `≥ 2` plus the three short
    -- strings gives `PP` membership.  `PolyTimeChecker R` is a HYPOTHESIS.
  ∧ (∀ (L : Language Bool) (R : Str × Str → Bool) (k : ℕ), 1 ≤ k → PolyTimeChecker R →
        (∀ x : Str, 2 ≤ x.length →
          (x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k))) →
        ([] ∈ L ↔ R ([], []) = true) →
        ([false] ∈ L ↔ (R ([false], [false]) = true ∧ R ([false], [true]) = true)) →
        ([true] ∈ L ↔ (R ([true], [false]) = true ∧ R ([true], [true]) = true)) →
        L ∈ PP)
    -- (7) the same, in the form a checker patched to CONSTANTS on the three short strings
    -- delivers.
  ∧ (∀ (L : Language Bool) (R : Str × Str → Bool) (k : ℕ) (c₀ c₁ c₂ : Bool),
        1 ≤ k → PolyTimeChecker R →
        (∀ x : Str, 2 ≤ x.length →
          (x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k))) →
        (∀ w : Str, R ([], w) = c₀) → (∀ w : Str, R ([false], w) = c₁) →
        (∀ w : Str, R ([true], w) = c₂) →
        (c₀ = true ↔ [] ∈ L) → (c₁ = true ↔ [false] ∈ L) → (c₂ = true ↔ [true] ∈ L) →
        L ∈ PP) := by
  refine ⟨ca0, ca1, maj0, maj1, fun R x c m hc => majConst R x c m hc,
    fun L R k hk hPT hlong hnil hf ht => glue L R k hk hPT hlong hnil hf ht, ?_⟩
  intro L R k c₀ c₁ c₂ hk hPT hlong h0 h1 h2 e0 e1 e2
  refine glue L R k hk hPT hlong ?_ ?_ ?_
  · rw [h0 []]
    exact e0.symm
  · rw [h1 [false], h1 [true]]
    constructor
    · intro hx
      exact ⟨e1.mpr hx, e1.mpr hx⟩
    · intro hx
      exact e1.mp hx.1
  · rw [h2 [false], h2 [true]]
    constructor
    · intro hx
      exact ⟨e2.mpr hx, e2.mpr hx⟩
    · intro hx
      exact e2.mp hx.1

end BQPReferenceValidation.Source24

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate24
    let target ← getConstInfo ``ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate24
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings; axioms {axioms}"
