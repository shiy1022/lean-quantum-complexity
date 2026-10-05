/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Uhlmann

/-!
# Q11 — Uhlmann for arbitrary environments, and monotonicity

* `norm_trace_mul_le_of_contraction`: `‖tr (C A)‖ ≤ tr |A|` for every contraction `Cᴴ C ≤ 1`
  (the unitary case is `norm_trace_mul_le`).
* `unitary_block12_contractions`: the off-diagonal block `B` of a unitary on `n ⊕ E` satisfies
  `B Bᴴ ≤ 1` and `Bᴴ B ≤ 1`.
* `exists_contraction_factor`: if `M Mᴴ = ρ` for `M : Matrix n E ℂ`, then `M = √ρ X` with
  `X Xᴴ ≤ 1` and `Xᴴ X ≤ 1`. The proof pads to `n ⊕ E` and uses `exists_unitary_padded`;
  `E` may be smaller or larger than `n`.
* `uhlmann_le_general`: **Uhlmann's upper bound for purifications on any environment `E`**.
* `fidelity_le_fidelity_traceRight`: **monotonicity**,
  `F (ρ_AB, σ_AB) ≤ F (Tr_B ρ_AB, Tr_B σ_AB)`. An optimal purification pair for the `AB` states
  (from `uhlmann_attained`) is re-read as a pair of purifications of the marginals, with
  environment `B × (A × B)`.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n E : Type} [Fintype n] [DecidableEq n] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
/-- **Trace bound for contractions.** -/
theorem norm_trace_mul_le_of_contraction {A C : Matrix n n ℂ} (hC : Cᴴ * C ≤ 1) :
    ‖trace (C * A)‖ ≤ (trace (absM A)).re := by
  obtain ⟨W, hW, hA⟩ := exists_polar A
  set P := absM A
  set Q := psdSqrt P
  have hQ : Q * Q = P := psdSqrt_mul_self (absM_posSemidef A)
  have hQh : Qᴴ = Q := psdSqrt_conjTranspose P
  have e1 : trace (C * A) = trace (Qᴴ * (C * W * Q)) := by
    rw [hQh]
    conv_lhs => rw [hA, ← hQ]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
  have e2 : (C * W * Q)ᴴ * (C * W * Q) = (Q * Wᴴ) * (Cᴴ * C) * (Q * Wᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, hQh, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e3 : (Q * Wᴴ) * 1 * (Q * Wᴴ)ᴴ = P := by
    rw [Matrix.mul_one, conjTranspose_mul, conjTranspose_conjTranspose, hQh, Matrix.mul_assoc,
      ← Matrix.mul_assoc Wᴴ, unitary_conjTranspose_mul hW, Matrix.one_mul, hQ]
  have hle : (trace ((C * W * Q)ᴴ * (C * W * Q))).re ≤ (trace P).re := by
    rw [e2, ← e3]
    exact re_trace_mono (conj_mono hC (Q * Wᴴ))
  have hcs := norm_trace_conjTranspose_mul_sq_le Q (C * W * Q)
  rw [← e1, show Qᴴ * Q = P by rw [hQh, hQ]] at hcs
  have hP0 : 0 ≤ (trace P).re := trace_absM_re_nonneg A
  have : ‖trace (C * A)‖ ^ 2 ≤ (trace P).re ^ 2 := by
    calc ‖trace (C * A)‖ ^ 2 ≤ (trace P).re * (trace ((C * W * Q)ᴴ * (C * W * Q))).re := hcs
      _ ≤ (trace P).re * (trace P).re := mul_le_mul_of_nonneg_left hle hP0
      _ = (trace P).re ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hP0 two_ne_zero).mp this

/-- The `(1, 2)` block of a unitary on `n ⊕ E` is a contraction from both sides. -/
theorem unitary_block12_contractions {U : Matrix (n ⊕ E) (n ⊕ E) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (n ⊕ E) ℂ) :
    U.toBlocks₁₂ * (U.toBlocks₁₂)ᴴ ≤ 1 ∧ (U.toBlocks₁₂)ᴴ * U.toBlocks₁₂ ≤ 1 := by
  have h1 := unitary_mul_conjTranspose hU
  have h2 := unitary_conjTranspose_mul hU
  constructor
  · have e : 1 - U.toBlocks₁₂ * (U.toBlocks₁₂)ᴴ = U.toBlocks₁₁ * (U.toBlocks₁₁)ᴴ := by
      ext a a'
      have := congrFun (congrFun h1 (Sum.inl a)) (Sum.inl a')
      simp only [mul_apply, conjTranspose_apply, Fintype.sum_sum_type, one_apply,
        Sum.inl.injEq] at this
      rw [Matrix.sub_apply, one_apply, ← this]
      simp only [mul_apply, conjTranspose_apply, toBlocks₁₁, toBlocks₁₂, of_apply]
      ring
    rw [Matrix.le_iff, e]
    exact posSemidef_self_mul_conjTranspose _
  · have e : 1 - (U.toBlocks₁₂)ᴴ * U.toBlocks₁₂ = (U.toBlocks₂₂)ᴴ * U.toBlocks₂₂ := by
      ext e e'
      have := congrFun (congrFun h2 (Sum.inr e)) (Sum.inr e')
      simp only [mul_apply, conjTranspose_apply, Fintype.sum_sum_type, one_apply,
        Sum.inr.injEq] at this
      rw [Matrix.sub_apply, one_apply, ← this]
      simp only [mul_apply, conjTranspose_apply, toBlocks₂₂, toBlocks₁₂, of_apply]
      ring
    rw [Matrix.le_iff, e]
    exact posSemidef_conjTranspose_mul_self _

/-- A factor `M` of `ρ = M Mᴴ` on any environment is `√ρ` times a contraction. -/
theorem exists_contraction_factor {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) {M : Matrix n E ℂ}
    (hM : M * Mᴴ = ρ) : ∃ X : Matrix n E ℂ, M = psdSqrt ρ * X ∧ X * Xᴴ ≤ 1 ∧ Xᴴ * X ≤ 1 := by
  have h : psdSqrt ρ * (psdSqrt ρ)ᴴ = M * Mᴴ := by rw [psdSqrt_mul_conjTranspose hρ, hM]
  obtain ⟨U, hU, hpad⟩ := exists_unitary_padded h
  refine ⟨U.toBlocks₁₂, ?_, unitary_block12_contractions hU⟩
  ext i e
  have := congrFun (congrFun hpad i) (Sum.inr e)
  rw [fromCols_apply_inr, mul_apply, Fintype.sum_sum_type] at this
  rw [this, mul_apply]
  simp [Matrix.zero_apply, toBlocks₁₂]

/-- **Uhlmann's upper bound on an arbitrary environment.** -/
theorem uhlmann_le_general {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {ψ φ : n × E → ℂ} (hψ : IsPurification ψ ρ) (hφ : IsPurification φ σ) :
    ‖star ψ ⬝ᵥ φ‖ ≤ fidelity ρ σ := by
  rw [isPurification_iff] at hψ hφ
  obtain ⟨X, hX, hXX, -⟩ := exists_contraction_factor hρ hψ
  obtain ⟨Y, hY, -, hYY⟩ := exists_contraction_factor hσ hφ
  have hψ' : ψ = matToVec (vecToMat ψ) := rfl
  have hφ' : φ = matToVec (vecToMat φ) := rfl
  rw [hψ', hφ', star_matToVec_dotProduct, hX, hY, conjTranspose_mul, psdSqrt_conjTranspose]
  have e : trace (Xᴴ * psdSqrt ρ * (psdSqrt σ * Y)) =
      trace (Y * Xᴴ * (psdSqrt ρ * psdSqrt σ)) := by
    rw [show Xᴴ * psdSqrt ρ * (psdSqrt σ * Y) = Xᴴ * ((psdSqrt ρ * psdSqrt σ) * Y) by
      simp only [Matrix.mul_assoc], trace_mul_comm, Matrix.mul_assoc, trace_mul_comm]
  rw [e]
  have hC : (Y * Xᴴ)ᴴ * (Y * Xᴴ) ≤ 1 := by
    have e2 : (Y * Xᴴ)ᴴ * (Y * Xᴴ) = X * (Yᴴ * Y) * Xᴴ := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
    rw [e2]
    calc X * (Yᴴ * Y) * Xᴴ ≤ X * 1 * Xᴴ := conj_mono hYY X
      _ = X * Xᴴ := by rw [Matrix.mul_one]
      _ ≤ 1 := hXX
  calc ‖trace (Y * Xᴴ * (psdSqrt ρ * psdSqrt σ))‖
      ≤ (trace (absM (psdSqrt ρ * psdSqrt σ))).re := norm_trace_mul_le_of_contraction hC
    _ = fidelity σ ρ := (fidelity_eq_traceNorm hρ).symm
    _ = fidelity ρ σ := fidelity_symm hσ hρ

/-! ## Monotonicity under partial trace -/

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Re-read a vector on `(A × B) × E` as a vector on `A × (B × E)`. -/
def reassocVec (ψ : (A × B) × E → ℂ) : A × (B × E) → ℂ := fun P => ψ ((P.1, P.2.1), P.2.2)

omit [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq E] in
theorem IsPurification.reassoc {ψ : (A × B) × E → ℂ} {ρ : Matrix (A × B) (A × B) ℂ}
    (h : IsPurification ψ ρ) : IsPurification (reassocVec ψ) (traceRight ρ) := by
  rw [IsPurification] at h ⊢
  rw [← h]
  ext a a'
  simp [pureState, vecMulVec_apply, reassocVec, Fintype.sum_prod_type]

omit [DecidableEq A] [DecidableEq B] [DecidableEq E] in
theorem reassocVec_dotProduct (ψ φ : (A × B) × E → ℂ) :
    star (reassocVec ψ) ⬝ᵥ reassocVec φ = star ψ ⬝ᵥ φ := by
  simp [dotProduct, reassocVec, Fintype.sum_prod_type]

/-- **Monotonicity of fidelity under partial trace.** -/
theorem fidelity_le_fidelity_traceRight {ρ σ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) : fidelity ρ σ ≤ fidelity (traceRight ρ) (traceRight σ) := by
  obtain ⟨φ, hφ, hov⟩ := uhlmann_attained hρ hσ
  have h1 := uhlmann_le_general (posSemidef_traceRight hρ) (posSemidef_traceRight hσ)
    (purify_isPurification hρ).reassoc hφ.reassoc
  rw [reassocVec_dotProduct, hov, Complex.norm_real,
    Real.norm_of_nonneg (fidelity_nonneg ρ σ)] at h1
  exact h1

end ShiQuantum
