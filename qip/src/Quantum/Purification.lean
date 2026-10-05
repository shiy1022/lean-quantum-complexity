/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.GramIsometry
import Quantum.PartialTrace

/-!
# Q09 — purification and equal-marginal unitaries

A vector `ψ : n × E → ℂ` on system `n` and environment `E` is the matrix
`vecToMat ψ : Matrix n E ℂ`. Its marginal on `n` is `vecToMat ψ * (vecToMat ψ)ᴴ`
(`traceRight_pureState`). `IsPurification ψ ρ` means this marginal is `ρ`.

* `purify ρ`: the canonical purification `(i, a) ↦ √ρ i a`, with environment `n`
  (`purify_isPurification`); it is normalized when `ρ` is a density operator
  (`IsPurification.isDensity`). Nothing assumes full rank.
* `exists_unitary_of_mul_conjTranspose_eq`: if `M Mᴴ = N Nᴴ` for `M, N : Matrix n E ℂ`, then
  `N = M U` for a **unitary** `U` on `E`. Hence two purifications of the same state on the same
  environment differ by a unitary on the environment alone
  (`IsPurification.exists_unitary`, also in vector form `(1 ⊗ Uᵀ) ψ = φ`).
* Different environments `E`, `F`: pad both to `E ⊕ F` with zero columns; then
  `exists_unitary_padded` gives a unitary on `E ⊕ F`. A same-size unitary is never claimed
  between environments of different dimensions.

Examples: a product `v ⊗ w` purifies the pure state `|v⟩⟨v|` (rank one), and the Bell vector
purifies the maximally mixed qubit.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker InnerProductSpace

variable {n E F : Type}

/-- A vector on `n × E` as a matrix `n × E`. -/
def vecToMat (ψ : n × E → ℂ) : Matrix n E ℂ := Matrix.of fun i e => ψ (i, e)

/-- A matrix `n × E` as a vector on `n × E`. -/
def matToVec (M : Matrix n E ℂ) : n × E → ℂ := fun P => M P.1 P.2

@[simp] theorem vecToMat_matToVec (M : Matrix n E ℂ) : vecToMat (matToVec M) = M := rfl

variable [Fintype n] [Fintype E] [Fintype F]

omit [Fintype n] in
theorem traceRight_pureState (ψ : n × E → ℂ) :
    traceRight (pureState ψ) = vecToMat ψ * (vecToMat ψ)ᴴ := by
  ext i j
  simp [pureState, vecMulVec_apply, mul_apply, vecToMat]

/-- `ψ` purifies `ρ`: tracing out the environment of `|ψ⟩⟨ψ|` leaves `ρ`. -/
def IsPurification (ψ : n × E → ℂ) (ρ : Matrix n n ℂ) : Prop := traceRight (pureState ψ) = ρ

omit [Fintype n] in
theorem isPurification_iff (ψ : n × E → ℂ) (ρ : Matrix n n ℂ) :
    IsPurification ψ ρ ↔ vecToMat ψ * (vecToMat ψ)ᴴ = ρ := by
  rw [IsPurification, traceRight_pureState]

/-- A purification of a density operator is a unit vector. -/
theorem IsPurification.isDensity {ψ : n × E → ℂ} {ρ : Matrix n n ℂ} (hψ : IsPurification ψ ρ)
    (hρ : IsDensity ρ) : IsDensity (pureState ψ) := by
  refine ⟨pureState_posSemidef ψ, ?_⟩
  rw [← trace_traceRight, hψ, hρ.trace_eq_one]

/-- The canonical purification `(i, a) ↦ √ρ i a`. -/
noncomputable def purify [DecidableEq n] (ρ : Matrix n n ℂ) : n × n → ℂ := matToVec (psdSqrt ρ)

/-- **Every PSD matrix has a purification** (no rank assumption). -/
theorem purify_isPurification [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    IsPurification (purify ρ) ρ := by
  rw [isPurification_iff, purify, vecToMat_matToVec, psdSqrt_mul_conjTranspose hρ]

theorem exists_purification [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) :
    ∃ ψ : n × n → ℂ, IsPurification ψ ρ ∧ IsDensity (pureState ψ) :=
  ⟨purify ρ, purify_isPurification hρ.posSemidef,
    (purify_isPurification hρ.posSemidef).isDensity hρ⟩

/-! ## Equal marginals -/

section Unitary

variable [DecidableEq E]

theorem conjTranspose_mul_self_apply (A : Matrix E E ℂ) (a b : E) :
    (Aᴴ * A) a b = star (A *ᵥ Pi.single a 1) ⬝ᵥ (A *ᵥ Pi.single b 1) := by
  simp [dotProduct, mul_apply, conjTranspose_apply]

theorem one_apply_eq_dotProduct (a b : E) :
    (1 : Matrix E E ℂ) a b = star (Pi.single a (1 : ℂ)) ⬝ᵥ Pi.single b 1 := by
  rw [dotProduct_single, mul_one, Pi.star_apply, one_apply, Pi.single_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The matrix of a linear isometry of `EuclideanSpace ℂ E` is unitary. -/
theorem linearIsometry_toMatrix_unitary (L : EuclideanSpace ℂ E →ₗᵢ[ℂ] EuclideanSpace ℂ E) :
    let A := LinearMap.toMatrix' ((WithLp.linearEquiv 2 ℂ (E → ℂ)).toLinearMap ∘ₗ
      L.toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℂ (E → ℂ)).symm.toLinearMap)
    (∀ v, A *ᵥ v = WithLp.ofLp (L (toE v))) ∧ Aᴴ * A = 1 := by
  intro A
  have hA : ∀ v, A *ᵥ v = WithLp.ofLp (L (toE v)) := fun v => by
    simp only [A, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rfl
  refine ⟨hA, ?_⟩
  ext a b
  have key := L.inner_map_map (toE (Pi.single a 1)) (toE (Pi.single b 1))
  have e1 : ∀ c, L (toE (Pi.single c 1)) = toE (A *ᵥ Pi.single c 1) := fun c => by
    rw [hA]
  rw [e1, e1, inner_toE, inner_toE] at key
  rw [conjTranspose_mul_self_apply, key, one_apply_eq_dotProduct]

/-- **Equal marginals ⇒ related by a unitary on the environment.** -/
theorem exists_unitary_of_mul_conjTranspose_eq {M N : Matrix n E ℂ} (h : M * Mᴴ = N * Nᴴ) :
    ∃ U ∈ Matrix.unitaryGroup E ℂ, N = M * U := by
  have hG : ∀ i j, ⟪toE (M i), toE (M j)⟫_ℂ = ⟪toE (N i), toE (N j)⟫_ℂ := by
    intro i j
    have := congrFun (congrFun h j) i
    simp only [mul_apply, conjTranspose_apply] at this
    rw [inner_toE, inner_toE, dotProduct_comm (star (M i)), dotProduct_comm (star (N i))]
    simpa [dotProduct] using this
  obtain ⟨L, hL⟩ := exists_linearIsometry_of_inner_eq hG
  obtain ⟨hA, hAA⟩ := linearIsometry_toMatrix_unitary L
  set A := LinearMap.toMatrix' ((WithLp.linearEquiv 2 ℂ (E → ℂ)).toLinearMap ∘ₗ
      L.toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℂ (E → ℂ)).symm.toLinearMap)
  have hAA' : A * Aᴴ = 1 := mul_eq_one_comm.mp hAA
  refine ⟨Aᵀ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
    have : (Aᵀ)ᴴ * Aᵀ = (A * Aᴴ)ᵀ := by
      ext a b; simp [mul_apply, conjTranspose_apply, mul_comm]
    rw [this, hAA', transpose_one]
  · have hrow : ∀ i, A *ᵥ M i = N i := fun i => by rw [hA, hL i]
    ext i f
    rw [← hrow i]
    simp [mulVec, dotProduct, mul_apply, mul_comm]

end Unitary

/-- Two purifications of the same state on the same environment differ by a unitary there. -/
theorem IsPurification.exists_unitary [DecidableEq E] {ψ φ : n × E → ℂ} {ρ : Matrix n n ℂ}
    (hψ : IsPurification ψ ρ) (hφ : IsPurification φ ρ) :
    ∃ U ∈ Matrix.unitaryGroup E ℂ, vecToMat φ = vecToMat ψ * U := by
  rw [isPurification_iff] at hψ hφ
  exact exists_unitary_of_mul_conjTranspose_eq (hψ.trans hφ.symm)

omit [Fintype F] in
/-- Vector form: right multiplication of `vecToMat ψ` by `U` is `(1 ⊗ Uᵀ) ψ`. -/
theorem matToVec_mul [DecidableEq n] (ψ : n × E → ℂ) (U : Matrix E F ℂ) :
    matToVec (vecToMat ψ * U) = ((1 : Matrix n n ℂ) ⊗ₖ Uᵀ) *ᵥ ψ := by
  funext ⟨i, f⟩
  simp [matToVec, mul_apply, vecToMat, mulVec, dotProduct, Fintype.sum_prod_type, one_apply,
    mul_comm]

/-! ## Different environments -/

omit [Fintype n] in
theorem fromCols_zero_mul_conjTranspose (M : Matrix n E ℂ) :
    fromCols M (0 : Matrix n F ℂ) * (fromCols M (0 : Matrix n F ℂ))ᴴ = M * Mᴴ := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
  simp

omit [Fintype n] in
theorem fromCols_zero_left_mul_conjTranspose (N : Matrix n F ℂ) :
    fromCols (0 : Matrix n E ℂ) N * (fromCols (0 : Matrix n E ℂ) N)ᴴ = N * Nᴴ := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
  simp

/-- **Different environments.** Pad `M : n × E` and `N : n × F` by zero columns to `E ⊕ F`; equal
marginals then give a unitary on the enlarged register `E ⊕ F`. -/
theorem exists_unitary_padded [DecidableEq E] [DecidableEq F] {M : Matrix n E ℂ}
    {N : Matrix n F ℂ} (h : M * Mᴴ = N * Nᴴ) :
    ∃ U ∈ Matrix.unitaryGroup (E ⊕ F) ℂ,
      fromCols (0 : Matrix n E ℂ) N = fromCols M (0 : Matrix n F ℂ) * U := by
  apply exists_unitary_of_mul_conjTranspose_eq
  rw [fromCols_zero_mul_conjTranspose, fromCols_zero_left_mul_conjTranspose, h]

/-! ## Examples -/

omit [Fintype n] in
/-- A product `v ⊗ w` with `w` a unit vector purifies the rank-one state `|v⟩⟨v|`. -/
theorem isPurification_product (v : n → ℂ) (w : E → ℂ) (hw : ∑ e, ‖w e‖ ^ 2 = 1) :
    IsPurification (fun P => v P.1 * w P.2) (pureState v) := by
  rw [IsPurification]
  ext i j
  have hw' : ∑ e, w e * star (w e) = 1 := by
    have : ∑ e, w e * star (w e) = ((∑ e, ‖w e‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun e _ => by rw [Complex.star_def, Complex.mul_conj']
    rw [this, hw]; simp
  simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply, star_mul']
  calc ∑ e, v i * w e * (star (v j) * star (w e))
      = v i * star (v j) * ∑ e, w e * star (w e) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
    _ = v i * star (v j) := by rw [hw', mul_one]

/-- The Bell vector purifies the maximally mixed qubit. -/
example : IsPurification bellVec (maxMixed Bool) := traceRight_bell

end ShiQuantum
