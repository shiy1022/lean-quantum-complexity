/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.ChannelTensor

/-!
# Q06 — bridge to Mathlib's `CompletelyPositiveMap`

Mathlib's `CompletelyPositiveMap A₁ A₂` asks that `M ↦ M.map φ` preserve `0 ≤ M` for every
`M : CStarMatrix (Fin k) (Fin k) A₁`. Here the order on `CStarMatrix` is the spectral order of its
C⋆-algebra structure. For `A₁ = Matrix m m ℂ` (with the `Matrix.Norms.L2Operator` C⋆-structure and
the `MatrixOrder` order) we show:

* `flat M : Matrix (k × m) (k × m) ℂ` flattens a block matrix (`flat_star_mul`:
  `flat (star N * N) = (flat N)ᴴ * flat N`);
* `cstar_nonneg_iff_flat`: `0 ≤ M ↔ (flat M).PosSemidef`;
* `flat_map`: `flat (M.map Φ) = liftR k Φ (flat M)`.

Hence `IsCP Φ ↔` Mathlib complete positivity (`isCP_iff_cpMap`), and `IsCP.toCPMap` packages a CP
map as a Mathlib `CompletelyPositiveMap`.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

variable {k m n : Type}

/-- Flatten a block matrix. -/
def flat (M : CStarMatrix k k (Matrix m m ℂ)) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun P Q => M P.1 Q.1 P.2 Q.2

/-- Unflatten a matrix on `k × m` into blocks. -/
def unflat (Y : Matrix (k × m) (k × m) ℂ) : CStarMatrix k k (Matrix m m ℂ) :=
  CStarMatrix.ofMatrix (Matrix.of fun a b => blockOf Y a b)

@[simp] theorem flat_unflat (Y : Matrix (k × m) (k × m) ℂ) : flat (unflat Y) = Y := by
  ext P Q; rfl

theorem flat_injective : Function.Injective (flat : CStarMatrix k k (Matrix m m ℂ) → _) := by
  intro M N h
  ext a b i j
  exact congrFun (congrFun h (a, i)) (b, j)

theorem flat_map (Φ : MatMap m n) (M : CStarMatrix k k (Matrix m m ℂ)) :
    flat (M.map Φ) = liftR k Φ (flat M) := by
  ext P Q; rfl

theorem liftR_reindex_fst {k' : Type} (e : k ≃ k') (Φ : MatMap m n)
    (X : Matrix (k × m) (k × m) ℂ) :
    liftR k' Φ (Matrix.reindex (e.prodCongr (Equiv.refl m)) (e.prodCongr (Equiv.refl m)) X) =
      Matrix.reindex (e.prodCongr (Equiv.refl n)) (e.prodCongr (Equiv.refl n)) (liftR k Φ X) := by
  ext P Q; rfl

theorem flat_star_mul [Fintype k] [Fintype m] (N : CStarMatrix k k (Matrix m m ℂ)) :
    flat (star N * N) = (flat N)ᴴ * flat N := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [flat, of_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.star_apply, conjTranspose_apply, Fintype.sum_prod_type]

variable [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/- Instance search does not find these two instances on `CStarMatrix` over a scoped C⋆-algebra;
the general C⋆-algebra instances apply when supplied explicitly. -/
theorem cstarMatrixCFC :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix k k (Matrix m m ℂ)) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

omit [DecidableEq k] in
theorem cstarMatrixNonnegSpectrum :
    NonnegSpectrumClass ℝ (CStarMatrix k k (Matrix m m ℂ)) :=
  CStarAlgebra.instNonnegSpectrumClass'

attribute [local instance] cstarMatrixCFC cstarMatrixNonnegSpectrum

/-- The C⋆-order on block matrices is positive semidefiniteness of the flattened matrix. -/
theorem cstar_nonneg_iff_flat (M : CStarMatrix k k (Matrix m m ℂ)) :
    0 ≤ M ↔ (flat M).PosSemidef := by
  constructor
  · intro hM
    obtain ⟨N, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    rw [flat_star_mul]
    exact posSemidef_conjTranspose_mul_self _
  · intro hM
    obtain ⟨B, hB⟩ := PSD_exists_eq_conjTranspose_mul hM
    have : M = star (unflat B) * unflat B := by
      apply flat_injective
      rw [flat_star_mul, flat_unflat, hB]
    rw [this]
    exact star_mul_self_nonneg _

/-- A CP map in the sense of `IsCP`, as a Mathlib `CompletelyPositiveMap`. -/
noncomputable def IsCP.toCPMap {Φ : MatMap m n} (h : IsCP Φ) :
    CompletelyPositiveMap (Matrix m m ℂ) (Matrix n n ℂ) where
  toLinearMap := Φ
  map_cstarMatrix_nonneg' j M hM := by
    rw [cstar_nonneg_iff_flat] at hM ⊢
    rw [flat_map]
    exact h (Fin j) _ hM

/-- **The bridge.** `IsCP` is exactly Mathlib's complete positivity on matrix algebras. -/
theorem isCP_iff_cpMap (Φ : MatMap m n) :
    IsCP Φ ↔ ∀ (j : ℕ) (M : CStarMatrix (Fin j) (Fin j) (Matrix m m ℂ)),
      0 ≤ M → 0 ≤ M.map Φ := by
  constructor
  · intro h j M hM
    exact h.toCPMap.map_cstarMatrix_nonneg' j M hM
  · intro h k' _ _ X hX
    let e := Fintype.equivFin k'
    let X' := Matrix.reindex (e.prodCongr (Equiv.refl m)) (e.prodCongr (Equiv.refl m)) X
    have hX' : X'.PosSemidef := by
      simp only [X', reindex_apply]; exact (posSemidef_submatrix_equiv _).mpr hX
    have hM : 0 ≤ unflat X' := by rw [cstar_nonneg_iff_flat, flat_unflat]; exact hX'
    have h1 := h _ (unflat X') hM
    rw [cstar_nonneg_iff_flat, flat_map, flat_unflat, liftR_reindex_fst, reindex_apply] at h1
    exact (posSemidef_submatrix_equiv _).mp h1

end ShiQuantum
