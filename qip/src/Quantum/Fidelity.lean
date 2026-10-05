/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Polar

/-!
# Q10 — root fidelity

**Convention (single, documented).** The *root* fidelity is

  `fidelity ρ σ = Re (trace (√(√ρ σ √ρ)))`,

a real number. Its square is written `fidelity ρ σ ^ 2` everywhere; no other notion of
"fidelity" is used.

* `fidelity_eq_traceNorm`: `fidelity ρ σ = Re tr |√σ √ρ|` (the trace norm of `√σ √ρ`);
* `fidelity_symm`: symmetry, through `tr |Aᴴ| = tr |A|` (polar decomposition);
* `fidelity_nonneg`, `fidelity_le_one`: `0 ≤ F ≤ 1` for density operators (Hilbert–Schmidt
  Cauchy–Schwarz at the optimal unitary);
* `fidelity_pure`: for unit vectors, `F (|ψ⟩⟨ψ|, |φ⟩⟨φ|) = ‖⟨ψ, φ⟩‖`, the absolute overlap;
* `prob_pure_eq_fidelity_sq`: the probability that `|φ⟩⟨φ|` accepts `|ψ⟩⟨ψ|` is the **square**
  `F ^ 2 = ‖⟨ψ, φ⟩‖ ^ 2`;
* `fidelity_diagonal`: for commuting diagonal states, `F = ∑ i, √(p i q i)`;
* `fidelity_kronecker`: multiplicativity under tensor products.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- Root fidelity `Re tr √(√ρ σ √ρ)`. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (trace (psdSqrt (psdSqrt ρ * σ * psdSqrt ρ))).re

theorem sandwich_eq {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    psdSqrt ρ * σ * psdSqrt ρ = (psdSqrt σ * psdSqrt ρ)ᴴ * (psdSqrt σ * psdSqrt ρ) := by
  rw [conjTranspose_mul, psdSqrt_conjTranspose, psdSqrt_conjTranspose]
  conv_lhs => rw [← psdSqrt_mul_self hσ]
  simp only [Matrix.mul_assoc]

theorem sandwich_posSemidef {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    (psdSqrt ρ * σ * psdSqrt ρ).PosSemidef := by
  have := conj_posSemidef hσ (psdSqrt ρ)
  rwa [psdSqrt_conjTranspose] at this

/-- The root fidelity is the trace norm of `√σ √ρ`. -/
theorem fidelity_eq_traceNorm {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    fidelity ρ σ = (trace (absM (psdSqrt σ * psdSqrt ρ))).re := by
  rw [fidelity, sandwich_eq hσ, absM]

theorem fidelity_symm {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    fidelity ρ σ = fidelity σ ρ := by
  rw [fidelity_eq_traceNorm hσ, fidelity_eq_traceNorm hρ, ← trace_absM_conjTranspose
    (psdSqrt ρ * psdSqrt σ), conjTranspose_mul, psdSqrt_conjTranspose, psdSqrt_conjTranspose]

theorem fidelity_nonneg (ρ σ : Matrix n n ℂ) : 0 ≤ fidelity ρ σ :=
  psd_trace_re_nonneg (psdSqrt_posSemidef _)

theorem fidelity_le_one {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    fidelity ρ σ ≤ 1 := by
  rw [fidelity_eq_traceNorm hσ.posSemidef]
  set A := psdSqrt σ * psdSqrt ρ
  obtain ⟨V, hV, hVA⟩ := exists_unitary_trace_eq_absM A
  have hre : (trace (absM A)).re = ‖trace (V * A)‖ := by
    rw [hVA, ← trace_absM_real A, Complex.norm_real, Real.norm_of_nonneg (trace_absM_re_nonneg A),
      Complex.ofReal_re]
  have hcs := norm_trace_conjTranspose_mul_sq_le (psdSqrt σ * Vᴴ) (psdSqrt ρ)
  have e1 : (psdSqrt σ * Vᴴ)ᴴ * psdSqrt ρ = V * A := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, psdSqrt_conjTranspose, Matrix.mul_assoc]
  have e2 : trace ((psdSqrt σ * Vᴴ)ᴴ * (psdSqrt σ * Vᴴ)) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, psdSqrt_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (psdSqrt σ), psdSqrt_mul_self hσ.posSemidef, ← Matrix.mul_assoc,
      trace_conj_unitary hV, hσ.trace_eq_one]
  have e3 : trace ((psdSqrt ρ)ᴴ * psdSqrt ρ) = 1 := by
    rw [psdSqrt_conjTranspose, psdSqrt_mul_self hρ.posSemidef, hρ.trace_eq_one]
  rw [e1, e2, e3, Complex.one_re, mul_one] at hcs
  rw [hre]
  nlinarith [norm_nonneg (trace (V * A))]

/-! ## Pure states -/

omit [DecidableEq n] in
theorem pureState_mul_self {v : n → ℂ} (hv : star v ⬝ᵥ v = 1) :
    pureState v * pureState v = pureState v := by
  rw [pureState, vecMulVec_mul_vecMulVec, hv, one_smul]

theorem psdSqrt_pureState {v : n → ℂ} (hv : star v ⬝ᵥ v = 1) :
    psdSqrt (pureState v) = pureState v :=
  psdSqrt_unique (pureState_posSemidef v) (pureState_mul_self hv)

omit [DecidableEq n] in
theorem star_dotProduct_swap (ψ φ : n → ℂ) : star φ ⬝ᵥ ψ = star (star ψ ⬝ᵥ φ) := by
  simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq n] in
theorem pure_sandwich {ψ φ : n → ℂ} :
    pureState ψ * pureState φ * pureState ψ =
      ((‖star ψ ⬝ᵥ φ‖ ^ 2 : ℝ) : ℂ) • pureState ψ := by
  rw [pureState, pureState, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, smul_dotProduct,
    smul_eq_mul, star_dotProduct_swap ψ φ, Complex.star_def, Complex.mul_conj']
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  push_cast; ring

/-- **Pure states**: the root fidelity is the absolute overlap. -/
theorem fidelity_pure {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    fidelity (pureState ψ) (pureState φ) = ‖star ψ ⬝ᵥ φ‖ := by
  rw [fidelity, psdSqrt_pureState hψ, pure_sandwich]
  set z := ‖star ψ ⬝ᵥ φ‖
  have hz : 0 ≤ z := norm_nonneg _
  have hsq : psdSqrt (((z ^ 2 : ℝ) : ℂ) • pureState ψ) = ((z : ℝ) : ℂ) • pureState ψ := by
    apply psdSqrt_unique
    · have := (pureState_posSemidef ψ).smul hz
      rwa [← Complex.coe_smul] at this
    · rw [smul_mul_smul_comm, pureState_mul_self hψ]
      push_cast; ring_nf
  rw [hsq, trace_smul, pureState, trace_rankOne, hψ, smul_eq_mul, mul_one, Complex.ofReal_re]

/-- **Acceptance is the square of the root fidelity.** -/
theorem prob_pure_eq_fidelity_sq {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    prob (pureState φ) (pureState ψ) = fidelity (pureState ψ) (pureState φ) ^ 2 := by
  rw [fidelity_pure hψ, prob_pureState, pureState, vecMulVec_mulVec]
  have : star ψ ⬝ᵥ (MulOpposite.op (star φ ⬝ᵥ ψ) • φ) = (star φ ⬝ᵥ ψ) * (star ψ ⬝ᵥ φ) := by
    set c := star φ ⬝ᵥ ψ
    conv_lhs => simp only [dotProduct, Pi.smul_apply, op_smul_eq_mul]
    conv_rhs => rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, star_dotProduct_swap ψ φ, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-! ## Commuting (diagonal) states -/

theorem psdSqrt_diagonal {p : n → ℝ} (hp : ∀ i, 0 ≤ p i) :
    psdSqrt (diagonal fun i => (p i : ℂ)) = diagonal fun i => ((Real.sqrt (p i) : ℝ) : ℂ) := by
  apply psdSqrt_unique
  · exact PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  · rw [diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp i)]

theorem fidelity_diagonal {p q : n → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    fidelity (diagonal fun i => (p i : ℂ)) (diagonal fun i => (q i : ℂ)) =
      ∑ i, Real.sqrt (p i * q i) := by
  rw [fidelity, psdSqrt_diagonal hp, diagonal_mul_diagonal, diagonal_mul_diagonal]
  have e : (fun i => ((Real.sqrt (p i) : ℝ) : ℂ) * (q i : ℂ) * ((Real.sqrt (p i) : ℝ) : ℂ)) =
      fun i => ((p i * q i : ℝ) : ℂ) := by
    funext i
    rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp i)]
    push_cast; ring
  rw [e, psdSqrt_diagonal fun i => mul_nonneg (hp i) (hq i)]
  simp [trace]

/-! ## Tensor products -/

theorem psdSqrt_kronecker {A : Matrix n n ℂ} {B : Matrix k k ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : psdSqrt (A ⊗ₖ B) = psdSqrt A ⊗ₖ psdSqrt B :=
  psdSqrt_unique ((psdSqrt_posSemidef A).kronecker (psdSqrt_posSemidef B)) (by
    rw [← mul_kronecker_mul, psdSqrt_mul_self hA, psdSqrt_mul_self hB])

theorem fidelity_kronecker {ρ₁ σ₁ : Matrix n n ℂ} {ρ₂ σ₂ : Matrix k k ℂ} (hρ₁ : ρ₁.PosSemidef)
    (hσ₁ : σ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef) (hσ₂ : σ₂.PosSemidef) :
    fidelity (ρ₁ ⊗ₖ ρ₂) (σ₁ ⊗ₖ σ₂) = fidelity ρ₁ σ₁ * fidelity ρ₂ σ₂ := by
  rw [fidelity, psdSqrt_kronecker hρ₁ hρ₂, ← mul_kronecker_mul, ← mul_kronecker_mul,
    psdSqrt_kronecker (sandwich_posSemidef hσ₁) (sandwich_posSemidef hσ₂), trace_kronecker,
    fidelity, fidelity, Complex.mul_re, psd_trace_im (psdSqrt_posSemidef _),
    psd_trace_im (psdSqrt_posSemidef _), mul_zero, sub_zero]

end ShiQuantum
