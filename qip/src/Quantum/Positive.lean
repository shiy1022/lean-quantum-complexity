/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Reindex

/-!
# Q03 — positive semidefinite matrices

Everything here is stated with Mathlib's own `Matrix.PosSemidef` and the Loewner order of scope
`MatrixOrder` (`A ≤ B ↔ (B - A).PosSemidef`); no competing positivity notion is introduced.

* factorization: a PSD matrix is `B * Bᴴ` and `Bᴴ * B` (`posSemidef_iff_exists_mul_conjTranspose`);
* the PSD square root `psdSqrt A = CFC.sqrt A`: PSD, Hermitian, squares to `A`, and unique;
* trace: invariance under reindexing and unitary conjugation, reality and nonnegativity on PSD
  matrices, `0 ≤ trace (A * B)` for PSD `A, B`, and monotonicity in the Loewner order;
* conjugation `A ↦ C * A * Cᴴ` and tensoring with a PSD matrix are monotone;
* rank-one matrices `|v⟩⟨v| = vecMulVec v (star v)`: PSD, `trace = ⟨v, v⟩ = ∑ ‖v i‖²`, and
  `trace (A |v⟩⟨v|) = ⟨v, A v⟩`.

The worked example `testMat = !![2, I; -I, 2]` is non-diagonal with complex entries.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {n m : Type*} [Fintype n] [Fintype m]

/-! ## Factorization -/

theorem PSD_exists_eq_conjTranspose_mul [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix n n ℂ, A = Bᴴ * B :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg

theorem PSD_exists_eq_mul_conjTranspose [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix n n ℂ, A = B * Bᴴ :=
  CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hA.nonneg

/-- A square matrix is PSD iff it factors as `B * Bᴴ`. -/
theorem posSemidef_iff_exists_mul_conjTranspose [DecidableEq n] {A : Matrix n n ℂ} :
    A.PosSemidef ↔ ∃ B : Matrix n n ℂ, A = B * Bᴴ :=
  ⟨PSD_exists_eq_mul_conjTranspose, fun ⟨B, h⟩ => h ▸ posSemidef_self_mul_conjTranspose B⟩

/-! ## The PSD square root -/

section Sqrt
variable [DecidableEq n]

/-- The positive square root, through Mathlib's continuous functional calculus. -/
noncomputable def psdSqrt (A : Matrix n n ℂ) : Matrix n n ℂ := CFC.sqrt A

theorem psdSqrt_posSemidef (A : Matrix n n ℂ) : (psdSqrt A).PosSemidef :=
  (CFC.sqrt_nonneg A).posSemidef

theorem psdSqrt_isHermitian (A : Matrix n n ℂ) : (psdSqrt A).IsHermitian :=
  (psdSqrt_posSemidef A).isHermitian

theorem psdSqrt_conjTranspose (A : Matrix n n ℂ) : (psdSqrt A)ᴴ = psdSqrt A :=
  (psdSqrt_isHermitian A).eq

theorem psdSqrt_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) : psdSqrt A * psdSqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem psdSqrt_mul_conjTranspose {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    psdSqrt A * (psdSqrt A)ᴴ = A := by
  rw [psdSqrt_conjTranspose, psdSqrt_mul_self hA]

/-- The PSD square root is the unique PSD matrix squaring to `A`. -/
theorem psdSqrt_unique {A B : Matrix n n ℂ} (hB : B.PosSemidef) (h : B * B = A) :
    psdSqrt A = B :=
  CFC.sqrt_unique h hB.nonneg

end Sqrt

/-! ## Trace -/

theorem trace_reindex {R : Type*} [AddCommMonoid R] (e : n ≃ m) (A : Matrix n n R) :
    trace (Matrix.reindex e e A) = trace A := by
  simp only [trace, reindex_apply, submatrix_apply, diag_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

theorem trace_conj_unitary [DecidableEq n] {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A : Matrix n n ℂ) : trace (U * A * Uᴴ) = trace A := by
  rw [trace_mul_cycle, ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU, one_mul]

theorem trace_permMat_conj [DecidableEq n] [DecidableEq m] (e : n ≃ m) (A : Matrix n n ℂ) :
    trace (permMat e * A * (permMat e)ᴴ) = trace A := by
  rw [permMat_conj, trace_reindex]

/-- The trace of a PSD matrix is a nonnegative real number. -/
theorem psd_trace_im {A : Matrix n n ℂ} (hA : A.PosSemidef) : (trace A).im = 0 :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm

theorem psd_trace_re_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ (trace A).re :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

theorem psd_ofReal_trace_re {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ((trace A).re : ℂ) = trace A :=
  Complex.ext rfl (by simp [psd_trace_im hA])

/-- `0 ≤ trace (A * B)` for PSD `A` and `B`. -/
theorem psd_trace_mul_nonneg [DecidableEq n] {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ trace (A * B) := by
  obtain ⟨X, rfl⟩ := PSD_exists_eq_mul_conjTranspose hA
  rw [Matrix.mul_assoc, trace_mul_comm]
  exact (hB.conjTranspose_mul_mul_same X).trace_nonneg

theorem psd_re_trace_mul_nonneg [DecidableEq n] {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (trace (A * B)).re :=
  (Complex.nonneg_iff.mp (psd_trace_mul_nonneg hA hB)).1

/-- The trace is monotone in the Loewner order. -/
theorem trace_mono {A B : Matrix n n ℂ} (h : A ≤ B) : trace A ≤ trace B := by
  have := (Matrix.le_iff.mp h).trace_nonneg
  rw [trace_sub] at this
  exact sub_nonneg.mp this

theorem re_trace_mono {A B : Matrix n n ℂ} (h : A ≤ B) : (trace A).re ≤ (trace B).re :=
  (Complex.le_def.mp (trace_mono h)).1

/-- Pairing with a PSD matrix is monotone: `A ≤ B → trace (A * P) ≤ trace (B * P)`. -/
theorem trace_mul_mono [DecidableEq n] {A B P : Matrix n n ℂ} (h : A ≤ B) (hP : P.PosSemidef) :
    trace (A * P) ≤ trace (B * P) := by
  have := psd_trace_mul_nonneg (Matrix.le_iff.mp h) hP
  rw [Matrix.sub_mul, trace_sub] at this
  exact sub_nonneg.mp this

/-! ## Monotonicity of conjugation and tensoring -/

theorem conj_mono {A B : Matrix n n ℂ} (h : A ≤ B) (C : Matrix m n ℂ) :
    C * A * Cᴴ ≤ C * B * Cᴴ := by
  rw [Matrix.le_iff] at h ⊢
  have := h.mul_mul_conjTranspose_same C
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this

theorem conj_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) (C : Matrix m n ℂ) :
    (C * A * Cᴴ).PosSemidef :=
  hA.mul_mul_conjTranspose_same C

theorem sub_kronecker' {n m : Type*} (A B : Matrix n n ℂ) (C : Matrix m m ℂ) :
    (B - A) ⊗ₖ C = B ⊗ₖ C - A ⊗ₖ C := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [sub_mul]

theorem kronecker_sub' {n m : Type*} (C : Matrix m m ℂ) (A B : Matrix n n ℂ) :
    C ⊗ₖ (B - A) = C ⊗ₖ B - C ⊗ₖ A := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [mul_sub]

theorem kronecker_mono_left {A B : Matrix n n ℂ} (h : A ≤ B) {C : Matrix m m ℂ}
    (hC : C.PosSemidef) : A ⊗ₖ C ≤ B ⊗ₖ C := by
  rw [Matrix.le_iff, ← sub_kronecker']
  exact (Matrix.le_iff.mp h).kronecker hC

theorem kronecker_mono_right {A B : Matrix n n ℂ} (h : A ≤ B) {C : Matrix m m ℂ}
    (hC : C.PosSemidef) : C ⊗ₖ A ≤ C ⊗ₖ B := by
  rw [Matrix.le_iff, ← kronecker_sub']
  exact hC.kronecker (Matrix.le_iff.mp h)

/-! ## Rank-one matrices -/

theorem rankOne_posSemidef (v : n → ℂ) : (vecMulVec v (star v)).PosSemidef :=
  posSemidef_vecMulVec_self_star v

theorem star_dotProduct_self' (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem trace_rankOne (v : n → ℂ) : trace (vecMulVec v (star v)) = star v ⬝ᵥ v := by
  rw [trace_vecMulVec, dotProduct_comm]

/-- `trace (A |v⟩⟨v|) = ⟨v, A v⟩`. -/
theorem trace_mul_rankOne (A : Matrix n n ℂ) (v : n → ℂ) :
    trace (A * vecMulVec v (star v)) = star v ⬝ᵥ (A *ᵥ v) := by
  simp only [trace, diag_apply, mul_apply, vecMulVec_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## A non-diagonal complex test matrix -/

/-- `!![2, I; -I, 2]`, eigenvalues `1` and `3`. -/
def testMat : Matrix (Fin 2) (Fin 2) ℂ := !![2, Complex.I; -Complex.I, 2]

/-- The vector `(1, -i)`, with `|v⟩⟨v| = !![1, I; -I, 1]`. -/
def testVec : Fin 2 → ℂ := ![1, -Complex.I]

theorem testMat_eq : testMat = 1 + vecMulVec testVec (star testVec) := by
  ext i j
  rw [Matrix.add_apply, vecMulVec_apply]
  fin_cases i <;> fin_cases j <;> simp [testMat, testVec] <;> norm_num

theorem testMat_posSemidef : testMat.PosSemidef := by
  rw [testMat_eq]
  exact PosSemidef.one.add (rankOne_posSemidef testVec)

example : trace testMat = 4 := by
  simp [testMat, trace, Fin.sum_univ_two]; norm_num

example : (psdSqrt testMat) * (psdSqrt testMat) = testMat := psdSqrt_mul_self testMat_posSemidef

example : 0 ≤ trace (testMat * vecMulVec testVec (star testVec)) :=
  psd_trace_mul_nonneg testMat_posSemidef (rankOne_posSemidef testVec)

/-- For `v = (1, -i)`, `testMat v = 3 v` and `⟨v, v⟩ = 2`, so `trace (testMat |v⟩⟨v|) = 6`,
computed through `trace_mul_rankOne`. -/
example : trace (testMat * vecMulVec testVec (star testVec)) = 6 := by
  rw [trace_mul_rankOne]
  simp [testMat, testVec, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  simp [Complex.ext_iff]
  norm_num

end ShiQuantum
