/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.UhlmannGeneral

/-!
# Q27 (scalar and fidelity part) — the Bell-test bound

* `fidelity_pureState_sq`: for PSD `ρ` and a unit vector `ψ`,
  `F(ρ, |ψ⟩⟨ψ|)² = ⟨ψ|ρ|ψ⟩`;
* `fidelity_diag_half_sq`: `F(diag(1-p, p), 1/2)² = 1/2 + √(p (1-p))`;
* `half_add_sqrt_le`: `1/2 + √(p (1-p)) ≤ 1 - (1/2 - p)²`;
* `bell_bound_third`: for `p ≤ 1/3`, the bound is at most `35/36`;
* `bell_prob_le`, `bell_prob_eq_one`: the abstract Bell test. After an isometry on everything
  but `B`, finding `(B, O)` in `|Φ⁺⟩` has probability at most `F(ρ_B, 1/2)²`. If `B` is
  maximally mixed, some isometry achieves probability one.
-/

namespace ShiQuantum

set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Fidelity with a pure state.** -/
theorem fidelity_pureState_sq {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) {ψ : n → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) : fidelity ρ (pureState ψ) ^ 2 = (star ψ ⬝ᵥ (ρ *ᵥ ψ)).re := by
  rw [fidelity_symm hρ (pureState_posSemidef ψ), fidelity, psdSqrt_pureState hψ]
  set c : ℂ := star ψ ⬝ᵥ (ρ *ᵥ ψ)
  have hc : 0 ≤ c := hρ.dotProduct_mulVec_nonneg ψ
  have hcre : 0 ≤ c.re := (Complex.nonneg_iff.mp hc).1
  have hcim : c.im = 0 := (Complex.nonneg_iff.mp hc).2.symm
  have hsand : pureState ψ * ρ * pureState ψ = c • pureState ψ := by
    rw [pureState, vecMulVec_mul, vecMulVec_mul_vecMulVec, ← dotProduct_mulVec]
    ext i j; simp [vecMulVec_apply, c]; ring
  have hcre' : c = ((c.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hcim])
  set z := Real.sqrt c.re
  have hsq : psdSqrt (c • pureState ψ) = ((z : ℝ) : ℂ) • pureState ψ := by
    apply psdSqrt_unique
    · have := (pureState_posSemidef ψ).smul (Real.sqrt_nonneg c.re)
      rwa [← Complex.coe_smul] at this
    · rw [smul_mul_smul_comm, pureState_mul_self hψ, hcre', ← Complex.ofReal_mul,
        Real.mul_self_sqrt hcre]
  rw [hsand, hsq, trace_smul, pureState, trace_rankOne, hψ, smul_eq_mul, mul_one,
    Complex.ofReal_re, Real.sq_sqrt hcre]

theorem fidelity_diag_half_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fidelity (diagonal fun b : Bool => (((if b then p else 1 - p) : ℝ) : ℂ))
        (diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ)) ^ 2 =
      1 / 2 + Real.sqrt (p * (1 - p)) := by
  rw [fidelity_diagonal (fun b => by split_ifs <;> linarith) (fun _ => by norm_num)]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  have h1 : 0 ≤ p * (1 / 2) := by positivity
  have h2 : 0 ≤ (1 - p) * (1 / 2) := by nlinarith
  rw [add_sq, Real.sq_sqrt h1, Real.sq_sqrt h2, mul_assoc, ← Real.sqrt_mul h1]
  have : p * (1 / 2) * ((1 - p) * (1 / 2)) = (p * (1 - p)) / 4 := by ring
  rw [this, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

/-- `1/2 + √(p(1-p)) ≤ 1 - (1/2 - p)²`. -/
theorem half_add_sqrt_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 / 2 + Real.sqrt (p * (1 - p)) ≤ 1 - (1 / 2 - p) ^ 2 := by
  set u := p * (1 - p)
  have hu : 0 ≤ u := mul_nonneg hp0 (by linarith)
  have hs := Real.sq_sqrt hu
  have key : Real.sqrt u ≤ 1 / 4 + u := by nlinarith [sq_nonneg (Real.sqrt u - 1 / 2)]
  have : 1 - (1 / 2 - p) ^ 2 = 3 / 4 + u := by simp only [u]; ring
  linarith

theorem bell_bound_third {p : ℝ} (hp : p ≤ 1 / 3) :
    1 - (1 / 2 - p) ^ 2 ≤ 35 / 36 := by
  nlinarith

/-! ## The Bell state -/

theorem sqrtTwo_inv_mul_self : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellVecB : Bool × Bool → ℂ := fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℂ))⁻¹ else 0

theorem bellVecB_norm : star bellVecB ⬝ᵥ bellVecB = 1 := by
  have h := sqrtTwo_inv_mul_self
  have hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  simp only [dotProduct, Pi.star_apply, bellVecB, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, star_zero, mul_zero,
    add_zero, zero_add, hs, h]
  norm_num

theorem traceRight_bellVecB :
    traceRight (pureState bellVecB) = diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ) := by
  have h := sqrtTwo_inv_mul_self
  have hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  ext a b
  simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply, bellVecB,
    Fintype.sum_bool, diagonal_apply]
  cases a <;> cases b <;> simp [hs, h]

/-- Reassociate `B × (O × R)` to `(B × O) × R`. -/
def assocVec {B O R : Type} (φ : B × (O × R) → ℂ) : (B × O) × R → ℂ :=
  fun p => φ (p.1.1, (p.1.2, p.2))

theorem traceRight_one_kron_mul_comm {α β β' : Type} [Fintype α] [Fintype β] [Fintype β']
    [DecidableEq α] (A : Matrix β' β ℂ) (X : Matrix (α × β) (α × β') ℂ) :
    traceRight (((1 : Matrix α α ℂ) ⊗ₖ A) * X) = traceRight (X * ((1 : Matrix α α ℂ) ⊗ₖ A)) := by
  ext a b
  simp only [traceRight_apply, mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_zero,
    Finset.sum_ite_eq', mul_one]
  have hL : ∀ x : β', (∑ x₁ : α, ∑ x₂ : β, if a = x₁ then A x x₂ * X (x₁, x₂) (b, x) else 0) =
      ∑ x₂, A x x₂ * X (a, x₂) (b, x) := by
    intro x; rw [Finset.sum_comm]; simp
  have hR : ∀ x : β, (∑ x₁ : α, ∑ x₂ : β', if x₁ = b then X (a, x) (x₁, x₂) * A x₂ x else 0) =
      ∑ x₂, X (a, x) (b, x₂) * A x₂ x := by
    intro x; rw [Finset.sum_comm]; simp
  rw [Finset.sum_congr rfl fun x _ => hL x, Finset.sum_congr rfl fun x _ => hR x, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem traceRight_conj_isometry {α β β' : Type} [Fintype α] [Fintype β] [Fintype β']
    [DecidableEq α] [DecidableEq β] (V : Matrix β' β ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix (α × β) (α × β) ℂ) :
    traceRight (((1 : Matrix α α ℂ) ⊗ₖ V) * M * ((1 : Matrix α α ℂ) ⊗ₖ V)ᴴ) = traceRight M := by
  rw [Matrix.mul_assoc, traceRight_one_kron_mul_comm, Matrix.mul_assoc, conjTranspose_kronecker,
    conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hV, one_kronecker_one, Matrix.mul_one]

theorem pureState_mulVec {α β : Type} [Fintype β] (A : Matrix α β ℂ) (v : β → ℂ) :
    pureState (A *ᵥ v) = A * pureState v * Aᴴ := by
  rw [pureState, pureState, mul_vecMulVec, vecMulVec_mul, star_mulVec]

theorem traceRight_traceRight_assoc {B O R : Type} [Fintype O] [Fintype R]
    (φ : B × (O × R) → ℂ) :
    traceRight (traceRight (pureState (assocVec φ))) = traceRight (pureState φ) := by
  ext a b
  simp [traceRight_apply, pureState, vecMulVec_apply, assocVec, Fintype.sum_prod_type]

variable {R R' : Type} [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']

/-- **Bell-test soundness (abstract).** After an isometry on everything but `B`, the
probability of finding `(B, O)` in `|Φ⁺⟩` is at most `F(ρ_B, 1/2)²`. -/
theorem bell_prob_le (ψ : Bool × R → ℂ) (V : Matrix (Bool × R') R ℂ) (hV : Vᴴ * V = 1) :
    (trace ((pureState bellVecB ⊗ₖ (1 : Matrix R' R' ℂ)) *
        pureState (assocVec (((1 : Matrix Bool Bool ℂ) ⊗ₖ V) *ᵥ ψ)))).re ≤
      fidelity (traceRight (pureState ψ)) (diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ)) ^ 2 := by
  set φ := assocVec (((1 : Matrix Bool Bool ℂ) ⊗ₖ V) *ᵥ ψ)
  set σ := traceRight (pureState φ)
  have hσ : σ.PosSemidef := posSemidef_traceRight (pureState_posSemidef φ)
  rw [← trace_mul_traceRight, trace_mul_comm,
    show pureState bellVecB = vecMulVec bellVecB (star bellVecB) from rfl, trace_mul_rankOne,
    ← fidelity_pureState_sq hσ bellVecB_norm]
  have hmono := fidelity_le_fidelity_traceRight hσ (pureState_posSemidef bellVecB)
  have hB : traceRight σ = traceRight (pureState ψ) := by
    rw [traceRight_traceRight_assoc, pureState_mulVec, traceRight_conj_isometry V hV]
  rw [hB, traceRight_bellVecB] at hmono
  exact pow_le_pow_left₀ (fidelity_nonneg _ _) hmono 2

/-- The embedding `r ↦ (0, r)`. -/
def embFalse (R : Type) [DecidableEq R] : Matrix (Bool × R) R ℂ :=
  Matrix.of fun p r => if p.1 = false ∧ p.2 = r then 1 else 0

theorem embFalse_isometry : (embFalse R)ᴴ * embFalse R = 1 := by
  ext r r'
  simp only [mul_apply, conjTranspose_apply, embFalse, of_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, one_apply]
  by_cases h : r = r' <;> simp [h, eq_comm]

/-- **Bell-test completeness (abstract).** If `B` is maximally mixed, an isometry on the
purifying system produces `|Φ⁺⟩` with certainty. -/
theorem bell_prob_eq_one [Nonempty R] (ψ : Bool × R → ℂ)
    (hψ : IsPurification ψ (diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ))) :
    ∃ V : Matrix (Bool × R) R ℂ, Vᴴ * V = 1 ∧
      (trace ((pureState bellVecB ⊗ₖ (1 : Matrix R R ℂ)) *
        pureState (assocVec (((1 : Matrix Bool Bool ℂ) ⊗ₖ V) *ᵥ ψ)))).re = 1 := by
  classical
  obtain ⟨r₀⟩ := ‹Nonempty R›
  set e : R → ℂ := Pi.single r₀ 1
  set τ : Bool × (Bool × R) → ℂ := fun p => bellVecB (p.1, p.2.1) * e p.2.2
  set ψ₁ := ((1 : Matrix Bool Bool ℂ) ⊗ₖ embFalse R) *ᵥ ψ
  have h₁ : IsPurification ψ₁ (diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ)) := by
    unfold IsPurification at hψ ⊢
    rw [pureState_mulVec, traceRight_conj_isometry _ embFalse_isometry, hψ]
  have hτ : IsPurification τ (diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ)) := by
    unfold IsPurification
    rw [← traceRight_bellVecB]
    ext a b
    simp only [traceRight_apply, pureState, vecMulVec_apply, τ, e, Fintype.sum_prod_type,
      Pi.star_apply, star_mul', Pi.single_apply]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_eq_single r₀]
    · simp
    · intro r _ hr; simp [hr]
    · simp
  obtain ⟨U, hU, hUeq⟩ := h₁.exists_unitary hτ
  have hτeq : τ = ((1 : Matrix Bool Bool ℂ) ⊗ₖ Uᵀ) *ᵥ ψ₁ := by
    rw [← matToVec_mul, ← hUeq]; rfl
  have hUt : (Uᵀ)ᴴ * Uᵀ = 1 := by
    have hu := Matrix.mem_unitaryGroup_iff.mp hU
    rw [star_eq_conjTranspose] at hu
    have : (Uᵀ)ᴴ = (Uᴴ)ᵀ := by ext i j; simp
    rw [this, ← transpose_mul, hu, transpose_one]
  refine ⟨Uᵀ * embFalse R, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Uᵀ)ᴴ, hUt, Matrix.one_mul,
      embFalse_isometry]
  · have hv : ((1 : Matrix Bool Bool ℂ) ⊗ₖ (Uᵀ * embFalse R)) *ᵥ ψ = τ := by
      rw [hτeq, mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul]
    rw [hv]
    have hp : pureState (assocVec τ) = pureState bellVecB ⊗ₖ pureState e := by
      ext ⟨⟨b, o⟩, r⟩ ⟨⟨b', o'⟩, r'⟩
      simp [pureState, vecMulVec_apply, assocVec, τ, kroneckerMap_apply, star_mul']; ring
    have hP : pureState bellVecB * pureState bellVecB = pureState bellVecB :=
      pureState_mul_self bellVecB_norm
    have he : star e ⬝ᵥ e = 1 := by simp [e, dotProduct, Pi.single_apply]
    rw [hp, ← mul_kronecker_mul, hP, Matrix.one_mul, trace_kronecker, pureState, pureState,
      trace_rankOne, trace_rankOne, bellVecB_norm, he]
    simp

end ShiQuantum
