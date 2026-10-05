import Quantum.Fidelity

/-! Fresh-import audit for Q10 (and the polar decomposition support): exact types, axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder Kronecker

#check (exists_polar : ∀ {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ),
  ∃ W ∈ Matrix.unitaryGroup n ℂ, A = W * absM A)
#check (norm_trace_mul_le : ∀ {n : Type} [Fintype n] [DecidableEq n] {A V : Matrix n n ℂ},
  V ∈ Matrix.unitaryGroup n ℂ → ‖trace (V * A)‖ ≤ (trace (absM A)).re)
#check (exists_unitary_trace_eq_absM : ∀ {n : Type} [Fintype n] [DecidableEq n]
  (A : Matrix n n ℂ), ∃ V ∈ Matrix.unitaryGroup n ℂ, trace (V * A) = trace (absM A))
#check (fidelity : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ → ℝ)
example {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) :
    fidelity ρ σ = (trace (psdSqrt (psdSqrt ρ * σ * psdSqrt ρ))).re := rfl
#check (fidelity_symm : ∀ {n : Type} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ},
  ρ.PosSemidef → σ.PosSemidef → fidelity ρ σ = fidelity σ ρ)
#check (fidelity_le_one : ∀ {n : Type} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ},
  IsDensity ρ → IsDensity σ → fidelity ρ σ ≤ 1)
#check (fidelity_pure : ∀ {n : Type} [Fintype n] [DecidableEq n] {ψ φ : n → ℂ},
  star ψ ⬝ᵥ ψ = 1 → fidelity (pureState ψ) (pureState φ) = ‖star ψ ⬝ᵥ φ‖)
#check (prob_pure_eq_fidelity_sq : ∀ {n : Type} [Fintype n] [DecidableEq n] {ψ φ : n → ℂ},
  star ψ ⬝ᵥ ψ = 1 → prob (pureState φ) (pureState ψ) = fidelity (pureState ψ) (pureState φ) ^ 2)

#print axioms ShiQuantum.absM_mul_self
#print axioms ShiQuantum.exists_polar
#print axioms ShiQuantum.conjTranspose_mem_unitaryGroup
#print axioms ShiQuantum.psdSqrt_mul_conjTranspose_eq
#print axioms ShiQuantum.trace_absM_conjTranspose
#print axioms ShiQuantum.trace_conjTranspose_mul_eq
#print axioms ShiQuantum.norm_trace_conjTranspose_mul_sq_le
#print axioms ShiQuantum.norm_trace_mul_le
#print axioms ShiQuantum.trace_polar_attains
#print axioms ShiQuantum.exists_unitary_trace_eq_absM
#print axioms ShiQuantum.sandwich_eq
#print axioms ShiQuantum.sandwich_posSemidef
#print axioms ShiQuantum.fidelity_eq_traceNorm
#print axioms ShiQuantum.fidelity_symm
#print axioms ShiQuantum.fidelity_nonneg
#print axioms ShiQuantum.fidelity_le_one
#print axioms ShiQuantum.pureState_mul_self
#print axioms ShiQuantum.psdSqrt_pureState
#print axioms ShiQuantum.pure_sandwich
#print axioms ShiQuantum.fidelity_pure
#print axioms ShiQuantum.prob_pure_eq_fidelity_sq
#print axioms ShiQuantum.psdSqrt_diagonal
#print axioms ShiQuantum.fidelity_diagonal
#print axioms ShiQuantum.psdSqrt_kronecker
#print axioms ShiQuantum.fidelity_kronecker
