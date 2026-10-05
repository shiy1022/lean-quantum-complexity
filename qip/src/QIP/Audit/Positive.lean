import Quantum.HilbertBridge

/-! Fresh-import audit for Q03: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder MatrixOrder

#check (posSemidef_iff_exists_mul_conjTranspose : ∀ {n : Type} [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ}, A.PosSemidef ↔ ∃ B : Matrix n n ℂ, A = B * Bᴴ)
#check (psdSqrt_unique : ∀ {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ},
  B.PosSemidef → B * B = A → psdSqrt A = B)
#check (psd_trace_mul_nonneg : ∀ {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ},
  A.PosSemidef → B.PosSemidef → 0 ≤ trace (A * B))
#check (conj_mono : ∀ {n m : Type} [Fintype n] [Fintype m] {A B : Matrix n n ℂ}, A ≤ B →
  ∀ C : Matrix m n ℂ, C * A * Cᴴ ≤ C * B * Cᴴ)
#check (trace_mul_rankOne : ∀ {n : Type} [Fintype n] (A : Matrix n n ℂ) (v : n → ℂ),
  trace (A * vecMulVec v (star v)) = star v ⬝ᵥ (A *ᵥ v))
#check (inner_toE : ∀ {n : Type} [Fintype n] (v w : n → ℂ),
  inner ℂ (toE v) (toE w) = star v ⬝ᵥ w)
#check (norm_toE_unitary : ∀ {n : Type} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ},
  U ∈ Matrix.unitaryGroup n ℂ → ∀ v : n → ℂ, ‖toE (U *ᵥ v)‖ = ‖toE v‖)

#print axioms ShiQuantum.PSD_exists_eq_conjTranspose_mul
#print axioms ShiQuantum.PSD_exists_eq_mul_conjTranspose
#print axioms ShiQuantum.posSemidef_iff_exists_mul_conjTranspose
#print axioms ShiQuantum.psdSqrt_posSemidef
#print axioms ShiQuantum.psdSqrt_conjTranspose
#print axioms ShiQuantum.psdSqrt_mul_self
#print axioms ShiQuantum.psdSqrt_mul_conjTranspose
#print axioms ShiQuantum.psdSqrt_unique
#print axioms ShiQuantum.trace_reindex
#print axioms ShiQuantum.trace_conj_unitary
#print axioms ShiQuantum.trace_permMat_conj
#print axioms ShiQuantum.psd_trace_im
#print axioms ShiQuantum.psd_trace_re_nonneg
#print axioms ShiQuantum.psd_ofReal_trace_re
#print axioms ShiQuantum.psd_trace_mul_nonneg
#print axioms ShiQuantum.psd_re_trace_mul_nonneg
#print axioms ShiQuantum.trace_mono
#print axioms ShiQuantum.re_trace_mono
#print axioms ShiQuantum.trace_mul_mono
#print axioms ShiQuantum.conj_mono
#print axioms ShiQuantum.conj_posSemidef
#print axioms ShiQuantum.kronecker_mono_left
#print axioms ShiQuantum.kronecker_mono_right
#print axioms ShiQuantum.rankOne_posSemidef
#print axioms ShiQuantum.star_dotProduct_self'
#print axioms ShiQuantum.trace_rankOne
#print axioms ShiQuantum.trace_mul_rankOne
#print axioms ShiQuantum.testMat_posSemidef
#print axioms ShiQuantum.inner_toE
#print axioms ShiQuantum.norm_toE_sq
#print axioms ShiQuantum.norm_toE_sq_eq_dotProduct
#print axioms ShiQuantum.norm_mulVec_le
#print axioms ShiQuantum.norm_toE_unitary
#print axioms ShiQuantum.inner_toE_mulVec_eq_trace
#print axioms ShiQuantum.psd_inner_nonneg
#print axioms ShiQuantum.supNorm_lt_norm_toE
