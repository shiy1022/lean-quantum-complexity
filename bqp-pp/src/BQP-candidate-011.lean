import Definitions.Def_ShiBQP_Core
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one
import Theorems.Thm_ShiShallow_gateCount_le_depth_mul_width_of_layerOk_core

namespace BQPReferenceValidation.Source11
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! POLY-DOM.  GATE-PREDICATE COUNTS ARE POLYNOMIALLY BOUNDED, AND EVERY POLYNOMIAL IS
DOMINATED BY A POWER -- FOR `n ≥ 2` AND NOT BELOW.

Two independent pieces, both needed by any reduction that has to fit a circuit statistic
inside the hard-coded witness length `x.length ^ k` of `ShiClassPP.PP`.

* **(1)-(3) THE COUNTING SIDE.**  For ANY per-gate predicate `p` -- in particular "is a
  Hadamard" -- the number of gates satisfying `p` in a circuit is at most the total gate
  count `(c.map List.length).sum`, which under well-formedness is at most `depth * width`
  (the published `gateCount_le_depth_mul_width_of_layerOk_core`).  For a well-formed family
  with depth and ancilla bound `q`, the explicit dominating polynomial is `q * (X + q + 1)`,
  exactly the witness of `FLATTEN-2b` (6)/(7).  Quantifying over `p` rather than fixing the
  Hadamard predicate costs nothing and makes the result reusable; (6) spells the Hadamard
  instance out.
* **(4) THE ARITHMETIC SIDE.**  `∀ r : Polynomial ℕ, ∃ k, ∀ n ≥ 2, 3 * r.eval n + 10 ≤ n ^ k`.
  The `+ 10` is the shape the assembly needs (`3 * (H + 1) + 7`).

**THE `n ≥ 2` SIDE CONDITION IS NOT AN ARTEFACT OF THE PROOF -- IT IS FORCED**, and (5)
says so as a theorem: for EVERY `r` and EVERY `k`, both `3 * r.eval 0 + 10 ≤ 0 ^ k` and
`3 * r.eval 1 + 10 ≤ 1 ^ k` are FALSE, since `0 ^ k ≤ 1` and `1 ^ k = 1` while the left side
is at least `10`.  A larger `k` cannot buy the short inputs; they need separate treatment.

HONEST LIMITATIONS.
1. Nothing here is quantum: `p` is an arbitrary Boolean predicate on instructions and no
   semantics of `Instr` is used.
2. `k` is produced from `r`'s `natDegree` and coefficient sum; no minimality is claimed.
3. No uniformity, no machine, and no `PP` membership is approached here.
-/

open ShiShallow ShiClass ShiBQP

/-! ### The counting side -/

/-- Any per-gate predicate counts at most the gate count. -/
private lemma countP_le_gateCount {n : ℕ} (p : Instr n → Bool) (c : Layered n) :
    c.flatten.countP p ≤ (c.map List.length).sum := by
  calc c.flatten.countP p ≤ c.flatten.length := List.countP_le_length
    _ = (c.map List.length).sum := List.length_flatten

/-- The witness polynomial, evaluated (as in `FLATTEN-2b`). -/
private lemma evalQ (q : Polynomial ℕ) (n : ℕ) :
    (q * (Polynomial.X + q + 1)).eval n = q.eval n * (n + q.eval n + 1) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one]

/-- For a well-formed family with depth/ancilla bound `q`, every gate-predicate count at
input length `n` is at most `(q * (X + q + 1)).eval n`. -/
private lemma famBound (F : Family) (hWF : WellFormed F) (q : Polynomial ℕ)
    (hd : ∀ n : ℕ, depth (F.circ n) ≤ q.eval n) (ha : ∀ n : ℕ, F.anc n ≤ q.eval n)
    (p : (n : ℕ) → Instr (n + (F.anc n + 1)) → Bool) (n : ℕ) :
    (F.circ n).flatten.countP (p n) ≤ (q * (Polynomial.X + q + 1)).eval n := by
  have h1 := countP_le_gateCount (p n) (F.circ n)
  have h2 := gateCount_le_depth_mul_width_of_layerOk_core (F.circ n) (hWF n)
  rw [evalQ]
  exact le_trans h1 (le_trans h2 (Nat.mul_le_mul (hd n) (by have := ha n; omega)))

/-! ### The arithmetic side -/

private lemma le_two_pow (x : ℕ) : x ≤ 2 ^ x := by
  induction x with
  | zero => norm_num
  | succ y ih =>
      have h1 : 1 ≤ 2 ^ y := Nat.one_le_pow y 2 (by norm_num)
      calc y + 1 ≤ 2 ^ y + 2 ^ y := Nat.add_le_add ih h1
        _ = 2 ^ (y + 1) := by ring

/-- A monomial-shaped bound dominates, with room for the additive `10`. -/
private lemma domAux (C d n : ℕ) (hn : 2 ≤ n) :
    3 * (C * n ^ d) + 10 ≤ n ^ (d + (3 * C + 10)) := by
  have hpow : 1 ≤ n ^ d := Nat.one_le_pow _ _ (by omega)
  have hB : (10 : ℕ) ≤ 10 * n ^ d := Nat.le_mul_of_pos_right _ hpow
  have hstep : 3 * (C * n ^ d) + 10 ≤ (3 * C + 10) * n ^ d := by
    calc 3 * (C * n ^ d) + 10 ≤ 3 * C * n ^ d + 10 * n ^ d :=
          Nat.add_le_add (Nat.le_of_eq (by ring)) hB
      _ = (3 * C + 10) * n ^ d := by ring
  have hD : 3 * C + 10 ≤ n ^ (3 * C + 10) :=
    le_trans (le_two_pow _) (Nat.pow_le_pow_left hn _)
  calc 3 * (C * n ^ d) + 10 ≤ (3 * C + 10) * n ^ d := hstep
    _ ≤ n ^ (3 * C + 10) * n ^ d := Nat.mul_le_mul hD (Nat.le_refl _)
    _ = n ^ (d + (3 * C + 10)) := by ring

/-- A polynomial over `ℕ` is bounded by its coefficient sum times `n ^ natDegree`, for
`n ≥ 1`. -/
private lemma evalLe (r : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    r.eval n ≤ (∑ i ∈ Finset.range (r.natDegree + 1), r.coeff i) * n ^ r.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))

private lemma polyDom (r : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n → 3 * r.eval n + 10 ≤ n ^ k := by
  refine ⟨r.natDegree + (3 * (∑ i ∈ Finset.range (r.natDegree + 1), r.coeff i) + 10),
    fun n hn => ?_⟩
  have h1 := evalLe r (le_trans (by norm_num) hn)
  exact le_trans (Nat.add_le_add (Nat.mul_le_mul (Nat.le_refl 3) h1) (Nat.le_refl 10))
    (domAux _ _ n hn)

theorem _root_.BQPReferenceValidation.candidate11 :
    -- (1) ANY per-gate predicate counts at most the gate count.
    (∀ (n : ℕ) (p : Instr n → Bool) (c : Layered n),
        c.flatten.countP p ≤ (c.map List.length).sum)
    -- (2) and for a well-formed circuit the gate count is at most depth times width.
  ∧ (∀ (n : ℕ) (c : Layered n), (∀ l ∈ c, LayerOk l) →
        (c.map List.length).sum ≤ depth c * n)
    -- (3) hence for a well-formed family with depth/ancilla bound `q`, every gate-predicate
    -- count is at most the EXPLICIT polynomial `q * (X + q + 1)`, evaluated at `n`.
  ∧ (∀ F : Family, WellFormed F → ∀ q : Polynomial ℕ,
        (∀ n : ℕ, depth (F.circ n) ≤ q.eval n) → (∀ n : ℕ, F.anc n ≤ q.eval n) →
        ∀ (p : (n : ℕ) → Instr (n + (F.anc n + 1)) → Bool) (n : ℕ),
          (F.circ n).flatten.countP (p n) ≤ (q * (Polynomial.X + q + 1)).eval n)
    -- (4) POLYNOMIAL DOMINATION.
  ∧ (∀ r : Polynomial ℕ, ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n → 3 * r.eval n + 10 ≤ n ^ k)
    -- (5) and the `n ≥ 2` side condition in (4) is FORCED: at `n = 0` and `n = 1` the
    -- inequality fails for EVERY `r` and EVERY `k`.
  ∧ (∀ (r : Polynomial ℕ) (k : ℕ),
        ¬ (3 * r.eval 0 + 10 ≤ 0 ^ k) ∧ ¬ (3 * r.eval 1 + 10 ≤ 1 ^ k))
    -- (6) COMBINED: for a well-formed, poly-bounded family, ONE `k` works for every
    -- input length `n ≥ 2`.
  ∧ (∀ F : Family, WellFormed F → PolyBounded F →
        ∀ p : (n : ℕ) → Instr (n + (F.anc n + 1)) → Bool, ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n →
          3 * ((F.circ n).flatten.countP (p n)) + 10 ≤ n ^ k)
    -- (7) the Hadamard instance of (6), spelled out.
  ∧ (∀ F : Family, WellFormed F → PolyBounded F → ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n →
        3 * ((F.circ n).flatten.countP
              (fun g => match g with | Instr.h _ => true | _ => false)) + 10 ≤ n ^ k) := by
  have h6 : ∀ F : Family, WellFormed F → PolyBounded F →
      ∀ p : (n : ℕ) → Instr (n + (F.anc n + 1)) → Bool, ∃ k : ℕ, ∀ n : ℕ, 2 ≤ n →
        3 * ((F.circ n).flatten.countP (p n)) + 10 ≤ n ^ k := by
    intro F hWF hPB p
    obtain ⟨q, hd, ha⟩ := hPB
    obtain ⟨k, hk⟩ := polyDom (q * (Polynomial.X + q + 1))
    refine ⟨k, fun n hn => ?_⟩
    have hb := famBound F hWF q hd ha p n
    exact le_trans
      (Nat.add_le_add (Nat.mul_le_mul (Nat.le_refl 3) hb) (Nat.le_refl 10)) (hk n hn)
  refine ⟨fun n p c => countP_le_gateCount p c,
    fun n c hc => gateCount_le_depth_mul_width_of_layerOk_core c hc,
    fun F hWF q hd ha p n => famBound F hWF q hd ha p n,
    polyDom, ?_, h6, ?_⟩
  · intro r k
    constructor
    · intro hcon
      have hz : (0 : ℕ) ^ k ≤ 1 := by
        calc (0 : ℕ) ^ k ≤ 1 ^ k := Nat.pow_le_pow_left (by norm_num) k
          _ = 1 := one_pow k
      have := le_trans hcon hz
      omega
    · intro hcon
      have ho : (1 : ℕ) ^ k = 1 := one_pow k
      rw [ho] at hcon
      omega
  · intro F hWF hPB
    exact h6 F hWF hPB _

end BQPReferenceValidation.Source11

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate11
    let target ← getConstInfo ``ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate11
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one; axioms {axioms}"
