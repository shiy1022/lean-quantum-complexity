/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Purification

/-!
# Q10/Q11 (support) — polar decomposition and trace optimization

For a square matrix `A` let `absM A = √(Aᴴ A)` (the PSD square root).

* `exists_polar`: `A = W * absM A` for a **unitary** `W`, with no rank assumption (zero singular
  values allowed). Proof: `Aᴴ` and `absM A` have the same marginal `Aᴴ A`, so the equal-marginal
  theorem of `Quantum.Purification` relates them by a unitary.
* `psdSqrt_mul_conjTranspose_eq`: `√(A Aᴴ) = W (absM A) Wᴴ`, hence
  `trace_absM_conjTranspose : trace (absM Aᴴ) = trace (absM A)`.
* `norm_trace_conjTranspose_mul_sq_le`: Hilbert–Schmidt Cauchy–Schwarz,
  `‖tr (Xᴴ Y)‖² ≤ Re tr (Xᴴ X) · Re tr (Yᴴ Y)`.
* **Trace optimization.** `norm_trace_mul_le`: `‖tr (V A)‖ ≤ Re tr (absM A)` for every unitary
  `V`; `trace_polar_attains`: `tr (Wᴴ A) = tr (absM A)` for the polar unitary, so the maximum is
  attained by an explicit unitary rather than being only a supremum.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `|A| = √(Aᴴ A)`. -/
noncomputable def absM (A : Matrix n n ℂ) : Matrix n n ℂ := psdSqrt (Aᴴ * A)

theorem absM_posSemidef (A : Matrix n n ℂ) : (absM A).PosSemidef := psdSqrt_posSemidef _

theorem absM_mul_self (A : Matrix n n ℂ) : absM A * absM A = Aᴴ * A :=
  psdSqrt_mul_self (posSemidef_conjTranspose_mul_self A)

theorem absM_conjTranspose_self (A : Matrix n n ℂ) : (absM A)ᴴ = absM A := psdSqrt_conjTranspose _

theorem unitary_conjTranspose_mul {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ) :
    Wᴴ * W = 1 := by
  rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hW

theorem unitary_mul_conjTranspose {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ) :
    W * Wᴴ = 1 := by
  rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hW

theorem conjTranspose_mem_unitaryGroup {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_conjTranspose]
  exact unitary_conjTranspose_mul hU

/-- **Polar decomposition** with a unitary factor. -/
theorem exists_polar (A : Matrix n n ℂ) :
    ∃ W ∈ Matrix.unitaryGroup n ℂ, A = W * absM A := by
  have h : absM A * (absM A)ᴴ = Aᴴ * Aᴴᴴ := by
    rw [absM_conjTranspose_self, absM_mul_self, conjTranspose_conjTranspose]
  obtain ⟨U, hU, hAU⟩ := exists_unitary_of_mul_conjTranspose_eq h
  refine ⟨Uᴴ, ?_, ?_⟩
  · exact conjTranspose_mem_unitaryGroup hU
  · have := congrArg conjTranspose hAU
    rw [conjTranspose_conjTranspose, conjTranspose_mul, absM_conjTranspose_self] at this
    exact this

/-- `√(A Aᴴ) = W |A| Wᴴ` for a polar unitary `W`. -/
theorem psdSqrt_mul_conjTranspose_eq {A W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ)
    (hA : A = W * absM A) : psdSqrt (A * Aᴴ) = W * absM A * Wᴴ := by
  apply psdSqrt_unique (conj_posSemidef (absM_posSemidef A) W)
  have e1 : W * absM A * Wᴴ * (W * absM A * Wᴴ) = W * (absM A * absM A) * Wᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, unitary_conjTranspose_mul hW, Matrix.one_mul]
  rw [e1]
  conv_rhs => rw [hA]
  rw [conjTranspose_mul, absM_conjTranspose_self]
  simp only [Matrix.mul_assoc]

/-- `tr √(A Aᴴ) = tr √(Aᴴ A)`. -/
theorem trace_absM_conjTranspose (A : Matrix n n ℂ) : trace (absM Aᴴ) = trace (absM A) := by
  obtain ⟨W, hW, hA⟩ := exists_polar A
  rw [absM, conjTranspose_conjTranspose, psdSqrt_mul_conjTranspose_eq hW hA,
    trace_conj_unitary hW]

/-! ## Hilbert–Schmidt Cauchy–Schwarz -/

/-- Vectorize a matrix. -/
def vecM (X : Matrix n n ℂ) : n × n → ℂ := fun P => X P.1 P.2

omit [DecidableEq n] in
theorem trace_conjTranspose_mul_eq (X Y : Matrix n n ℂ) :
    trace (Xᴴ * Y) = star (vecM X) ⬝ᵥ vecM Y := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, dotProduct, vecM, Pi.star_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq n] in
/-- **Hilbert–Schmidt Cauchy–Schwarz.** -/
theorem norm_trace_conjTranspose_mul_sq_le (X Y : Matrix n n ℂ) :
    ‖trace (Xᴴ * Y)‖ ^ 2 ≤ (trace (Xᴴ * X)).re * (trace (Yᴴ * Y)).re := by
  have hx : (trace (Xᴴ * X)).re = ‖toE (vecM X)‖ ^ 2 := by
    rw [trace_conjTranspose_mul_eq, ← norm_toE_sq_eq_dotProduct, Complex.ofReal_re]
  have hy : (trace (Yᴴ * Y)).re = ‖toE (vecM Y)‖ ^ 2 := by
    rw [trace_conjTranspose_mul_eq, ← norm_toE_sq_eq_dotProduct, Complex.ofReal_re]
  rw [hx, hy, trace_conjTranspose_mul_eq, ← inner_toE, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-! ## Trace optimization over unitaries -/

theorem trace_absM_re_nonneg (A : Matrix n n ℂ) : 0 ≤ (trace (absM A)).re :=
  psd_trace_re_nonneg (absM_posSemidef A)

theorem trace_absM_real (A : Matrix n n ℂ) : ((trace (absM A)).re : ℂ) = trace (absM A) :=
  psd_ofReal_trace_re (absM_posSemidef A)

/-- **Upper bound**: `‖tr (V A)‖ ≤ tr |A|` for every unitary `V`. -/
theorem norm_trace_mul_le {A V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ‖trace (V * A)‖ ≤ (trace (absM A)).re := by
  obtain ⟨W, hW, hA⟩ := exists_polar A
  set P := absM A
  set Q := psdSqrt P
  have hQ : Q * Q = P := psdSqrt_mul_self (absM_posSemidef A)
  have hQh : Qᴴ = Q := psdSqrt_conjTranspose P
  have e1 : trace (V * A) = trace (Qᴴ * (V * W * Q)) := by
    rw [hQh]
    conv_lhs => rw [hA, ← hQ]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
  have e2 : (V * W * Q)ᴴ * (V * W * Q) = P := by
    rw [conjTranspose_mul, conjTranspose_mul, hQh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, unitary_conjTranspose_mul hV, Matrix.one_mul,
      ← Matrix.mul_assoc Wᴴ W, unitary_conjTranspose_mul hW, Matrix.one_mul, hQ]
  have e3 : Qᴴ * Q = P := by rw [hQh, hQ]
  have hcs := norm_trace_conjTranspose_mul_sq_le Q (V * W * Q)
  rw [← e1, e2, e3, ← sq] at hcs
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (trace_absM_re_nonneg A) two_ne_zero).mp hcs

/-- **The maximum is attained** by the conjugate of the polar unitary. -/
theorem trace_polar_attains {A W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ)
    (hA : A = W * absM A) : trace (Wᴴ * A) = trace (absM A) := by
  conv_lhs => rw [hA]
  rw [← Matrix.mul_assoc, unitary_conjTranspose_mul hW, Matrix.one_mul]

/-- `tr |A| = max over unitaries V of ‖tr (V A)‖`, with an explicit maximizer. -/
theorem exists_unitary_trace_eq_absM (A : Matrix n n ℂ) :
    ∃ V ∈ Matrix.unitaryGroup n ℂ, trace (V * A) = trace (absM A) := by
  obtain ⟨W, hW, hA⟩ := exists_polar A
  exact ⟨Wᴴ, conjTranspose_mem_unitaryGroup hW, trace_polar_attains hW hA⟩

end ShiQuantum
