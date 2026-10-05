/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Positive

/-!
# Q03 — coordinate vectors and the Hilbert-space structure

Quantum states are coordinate functions `v : n → ℂ`, but the norm Lean puts on a raw function
type is the **sup norm**, not the Hilbert norm. Every norm or inner-product statement about states
therefore goes through `toE v = WithLp.toLp 2 v : EuclideanSpace ℂ n`:

* `inner_toE : ⟪toE v, toE w⟫ = star v ⬝ᵥ w` (conjugate-linear in the first argument);
* `norm_toE_sq : ‖toE v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2`;
* `toEuclideanLin_toE`: matrix action agrees with `mulVec`;
* `norm_mulVec_le`: under `Matrix.Norms.L2Operator`, `‖A v‖ ≤ ‖A‖ ‖v‖` (the operator norm);
* `norm_toE_unitary`: unitaries preserve the Hilbert norm;
* `inner_toE_mulVec_eq_trace`: `⟪v, A v⟫ = trace (A |v⟩⟨v|)`, and it is nonnegative for PSD `A`.

`supNorm_lt_norm_toE` exhibits the discrepancy: for `v = (1, 1)` the sup norm is `1` while the
Hilbert norm is `√2`.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n]

/-- A coordinate vector viewed in the Euclidean (Hilbert) space. -/
abbrev toE (v : n → ℂ) : EuclideanSpace ℂ n := WithLp.toLp 2 v

omit [Fintype n] in
@[simp] theorem toE_apply (v : n → ℂ) (i : n) : toE v i = v i := rfl

theorem inner_toE (v w : n → ℂ) : inner ℂ (toE v) (toE w) = star v ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

theorem norm_toE_sq (v : n → ℂ) : ‖toE v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem norm_toE_sq_eq_dotProduct (v : n → ℂ) : ((‖toE v‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  rw [star_dotProduct_self', norm_toE_sq]

theorem toEuclideanLin_toE [DecidableEq n] (A : Matrix n n ℂ) (v : n → ℂ) :
    Matrix.toEuclideanLin A (toE v) = toE (A *ᵥ v) := rfl

section L2
open scoped Matrix.Norms.L2Operator

/-- The L2 operator norm bounds the Hilbert norm of `A v`. -/
theorem norm_mulVec_le [DecidableEq n] (A : Matrix n n ℂ) (v : n → ℂ) :
    ‖toE (A *ᵥ v)‖ ≤ ‖A‖ * ‖toE v‖ :=
  Matrix.l2_opNorm_mulVec A (toE v)

end L2

/-- Unitaries preserve the Hilbert norm. -/
theorem norm_toE_unitary [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (v : n → ℂ) : ‖toE (U *ᵥ v)‖ = ‖toE v‖ := by
  have key : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp hU, vecMul_one]
  have h2 : ‖toE (U *ᵥ v)‖ ^ 2 = ‖toE v‖ ^ 2 := by
    have := (norm_toE_sq_eq_dotProduct (U *ᵥ v)).trans (key.trans
      (norm_toE_sq_eq_dotProduct v).symm)
    exact_mod_cast this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The quadratic form is the trace pairing with a rank-one matrix. -/
theorem inner_toE_mulVec_eq_trace (A : Matrix n n ℂ) (v : n → ℂ) :
    inner ℂ (toE v) (toE (A *ᵥ v)) = trace (A * vecMulVec v (star v)) := by
  rw [inner_toE, trace_mul_rankOne]

theorem psd_inner_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (v : n → ℂ) :
    0 ≤ inner ℂ (toE v) (toE (A *ᵥ v)) := by
  rw [inner_toE]
  exact hA.dotProduct_mulVec_nonneg v

/-- The default norm on `Fin 2 → ℂ` is the sup norm, strictly smaller than the Hilbert norm on
`(1, 1)`: the two must not be confused. -/
theorem supNorm_lt_norm_toE : ‖(fun _ => 1 : Fin 2 → ℂ)‖ < ‖toE (fun _ => 1 : Fin 2 → ℂ)‖ := by
  have hsup : ‖(fun _ => 1 : Fin 2 → ℂ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hE : ‖toE (fun _ => 1 : Fin 2 → ℂ)‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    simp
  rw [hE]
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt zero_le_one]; norm_num
  linarith

end ShiQuantum
