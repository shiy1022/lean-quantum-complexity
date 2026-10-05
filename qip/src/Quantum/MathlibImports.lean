/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Mathlib

/-!
# Q01 — the pinned Mathlib API used by the quantum development

Every declaration listed in `verification/mathlib-api.md` as "available" is `#check`ed here, so
compiling this module confirms that the name exists with the recorded scope. The `example`s
confirm the instance plumbing the later tasks rely on (scopes `ComplexOrder`, `MatrixOrder`,
`Matrix.Norms.L2Operator`, `Kronecker`, `CStarAlgebra`), on non-diagonal complex matrices where
that matters. Absences (partial trace, Choi/Kraus, fidelity, trace norm, polar decomposition,
SDP duality, rectangular isometries) are recorded in the inventory, not here.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## 1. Positive semidefinite matrices -/

#check @Matrix.PosSemidef
#check @Matrix.PosDef
#check @Matrix.posSemidef_iff_dotProduct_mulVec
#check @Matrix.PosSemidef.dotProduct_mulVec_nonneg
#check @Matrix.PosSemidef.submatrix
#check @Matrix.posSemidef_submatrix_equiv
#check @Matrix.PosSemidef.conjTranspose_mul_mul_same
#check @Matrix.PosSemidef.mul_mul_conjTranspose_same
#check @Matrix.PosSemidef.trace_nonneg
#check @Matrix.posSemidef_conjTranspose_mul_self
#check @Matrix.posSemidef_self_mul_conjTranspose
#check @Matrix.PosSemidef.eigenvalues_nonneg
#check @Matrix.PosSemidef.trace_eq_zero_iff
#check @Matrix.PosSemidef.kronecker
#check @Matrix.posSemidef_iff_eq_sum_vecMulVec
#check @Matrix.isPositive_toEuclideanLin_iff
#check @CStarAlgebra.nonneg_iff_eq_star_mul_self

/-! ## 2. Loewner order (scope `MatrixOrder`) -/

#check @Matrix.le_iff
#check @Matrix.nonneg_iff_posSemidef
#check @Matrix.PosSemidef.nonneg
#check @Matrix.instStarOrderedRing

/-- The Loewner order is `B - A` positive semidefinite. -/
example (A B : Matrix (Fin 2) (Fin 2) ℂ) : A ≤ B ↔ (B - A).PosSemidef := Matrix.le_iff

/-! ## 3. Hermitian spectral theory -/

#check @Matrix.IsHermitian.eigenvalues
#check @Matrix.IsHermitian.eigenvectorBasis
#check @Matrix.IsHermitian.eigenvectorUnitary
#check @Matrix.IsHermitian.spectral_theorem
#check @Matrix.IsHermitian.trace_eq_sum_eigenvalues

/-! ## 4. Trace -/

#check @Matrix.trace_mul_comm
#check @Matrix.trace_mul_cycle
#check @Matrix.trace_conjTranspose
#check @Matrix.trace_transpose
#check @Matrix.trace_kronecker

/-! ## 5–6. Norms and inner products -/

#check @Matrix.toEuclideanLin
#check @EuclideanSpace.inner_eq_star_dotProduct
#check @Matrix.dotProduct_mulVec
#check @CStarMatrix

section L2
open scoped Matrix.Norms.L2Operator

#check @Matrix.toEuclideanCLM
#check @Matrix.l2_opNorm_def
#check @Matrix.cstar_norm_def
#check @Matrix.l2_opNorm_mulVec
#check @Matrix.l2_opNorm_conjTranspose_mul_self

/-- Under `Matrix.Norms.L2Operator` the norm is the Euclidean operator norm. -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖A‖ = ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin 2) (n := Fin 2)).trans
      LinearMap.toContinuousLinearMap A‖ := Matrix.l2_opNorm_def A

/-- `Matrix n n ℂ` is a C⋆-algebra under the L2 operator norm, so CP maps between matrix
algebras are expressible. -/
example : Type := CompletelyPositiveMap (Matrix (Fin 2) (Fin 2) ℂ) (Matrix (Fin 3) (Fin 3) ℂ)

end L2

/-! ## 7. Completely positive and positive maps -/

#check @CompletelyPositiveMap
#check @CompletelyPositiveMap.map_cstarMatrix_nonneg
#check @PositiveLinearMap.mk₀

/-! ## 8. Kronecker products -/

#check @Matrix.mul_kronecker_mul
#check @Matrix.kronecker_assoc
#check @Matrix.conjTranspose_kronecker

/-! ## 9. Unitaries -/

#check @Matrix.mem_unitaryGroup_iff
#check @Matrix.kronecker_mem_unitary

/-! ## 10. Compactness and separation -/

#check @Metric.isCompact_of_isClosed_isBounded
#check @FiniteDimensional.proper_rclike
#check @IsCompact.exists_isMaxOn
#check @geometric_hahn_banach_point_closed
#check @RCLike.geometric_hahn_banach_point_closed
#check @ProperCone.hyperplane_separation
#check @ProperCone.hyperplane_separation'
#check @ProperCone.innerDual
#check @ProperCone.relative_hyperplane_separation

/-! ## 11. Singular values and absolute values -/

#check @LinearMap.singularValues
#check @CFC.abs

/-! ## 12. Functional calculus and square roots -/

#check @Matrix.IsHermitian.cfc
#check @Matrix.IsHermitian.cfc_eq
#check @CFC.sqrt
#check @CFC.sqrt_nonneg
#check @CFC.sqrt_mul_sqrt_self

/-- A non-diagonal Hermitian matrix: `[[2, i], [-i, 2]]`. -/
example : (!![2, Complex.I; -Complex.I, 2] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- The PSD square root exists on complex matrices, squares back, and is PSD. -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A ∧ (CFC.sqrt A).PosSemidef :=
  ⟨CFC.sqrt_mul_sqrt_self A hA.nonneg, (CFC.sqrt_nonneg A).posSemidef⟩

/-- Every PSD matrix factors as `Bᴴ * B` (through the C⋆-algebra lemma, `star = ᴴ`). -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) : ∃ B, A = Bᴴ * B :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
