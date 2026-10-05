import Quantum.Purification

/-! Fresh-import audit for Q09: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder InnerProductSpace

#check (exists_linearIsometry_of_inner_eq : ∀ {V : Type} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {ι : Type} [Fintype ι] {x y : ι → V},
  (∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ) → ∃ L : V →ₗᵢ[ℂ] V, ∀ i, L (x i) = y i)
#check (purify_isPurification : ∀ {n : Type} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ},
  ρ.PosSemidef → IsPurification (purify ρ) ρ)
#check (exists_unitary_of_mul_conjTranspose_eq : ∀ {n E : Type} [Fintype n] [Fintype E]
  [DecidableEq E] {M N : Matrix n E ℂ}, M * Mᴴ = N * Nᴴ →
  ∃ U ∈ Matrix.unitaryGroup E ℂ, N = M * U)
#check (exists_unitary_padded : ∀ {n E F : Type} [Fintype n] [Fintype E] [Fintype F]
  [DecidableEq E] [DecidableEq F] {M : Matrix n E ℂ} {N : Matrix n F ℂ}, M * Mᴴ = N * Nᴴ →
  ∃ U ∈ Matrix.unitaryGroup (E ⊕ F) ℂ,
    fromCols (0 : Matrix n E ℂ) N = fromCols M (0 : Matrix n F ℂ) * U)

#print axioms ShiQuantum.inner_linearCombination
#print axioms ShiQuantum.norm_linearCombination_eq
#print axioms ShiQuantum.exists_linearIsometry_of_inner_eq
#print axioms ShiQuantum.traceRight_pureState
#print axioms ShiQuantum.isPurification_iff
#print axioms ShiQuantum.IsPurification.isDensity
#print axioms ShiQuantum.purify_isPurification
#print axioms ShiQuantum.exists_purification
#print axioms ShiQuantum.conjTranspose_mul_self_apply
#print axioms ShiQuantum.one_apply_eq_dotProduct
#print axioms ShiQuantum.linearIsometry_toMatrix_unitary
#print axioms ShiQuantum.exists_unitary_of_mul_conjTranspose_eq
#print axioms ShiQuantum.IsPurification.exists_unitary
#print axioms ShiQuantum.matToVec_mul
#print axioms ShiQuantum.fromCols_zero_mul_conjTranspose
#print axioms ShiQuantum.fromCols_zero_left_mul_conjTranspose
#print axioms ShiQuantum.exists_unitary_padded
#print axioms ShiQuantum.isPurification_product
