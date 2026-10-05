import Quantum.UhlmannGeneral

/-! Fresh-import audit for Q11 (common-environment part): exact statement types, axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder

#check (uhlmann_le : ∀ {n : Type} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ},
  ρ.PosSemidef → σ.PosSemidef → ∀ {ψ φ : n × n → ℂ}, IsPurification ψ ρ →
  IsPurification φ σ → ‖star ψ ⬝ᵥ φ‖ ≤ fidelity ρ σ)
#check (uhlmann_attained : ∀ {n : Type} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ},
  ρ.PosSemidef → σ.PosSemidef → ∃ φ : n × n → ℂ, IsPurification φ σ ∧
    star (purify ρ) ⬝ᵥ φ = (fidelity ρ σ : ℂ))

#print axioms ShiQuantum.star_matToVec_dotProduct
#print axioms ShiQuantum.uhlmann_le
#print axioms ShiQuantum.uhlmann_attained
#print axioms ShiQuantum.fidelity_eq_max_overlap

/-! Arbitrary environments and monotonicity. -/

#check (uhlmann_le_general : ∀ {n E : Type} [Fintype n] [DecidableEq n] [Fintype E]
  [DecidableEq E] {ρ σ : Matrix n n ℂ}, ρ.PosSemidef → σ.PosSemidef → ∀ {ψ φ : n × E → ℂ},
  IsPurification ψ ρ → IsPurification φ σ → ‖star ψ ⬝ᵥ φ‖ ≤ fidelity ρ σ)
#check (fidelity_le_fidelity_traceRight : ∀ {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {ρ σ : Matrix (A × B) (A × B) ℂ}, ρ.PosSemidef → σ.PosSemidef →
  fidelity ρ σ ≤ fidelity (ShiQuantum.traceRight ρ) (ShiQuantum.traceRight σ))

#print axioms ShiQuantum.norm_trace_mul_le_of_contraction
#print axioms ShiQuantum.unitary_block12_contractions
#print axioms ShiQuantum.exists_contraction_factor
#print axioms ShiQuantum.uhlmann_le_general
#print axioms ShiQuantum.IsPurification.reassoc
#print axioms ShiQuantum.reassocVec_dotProduct
#print axioms ShiQuantum.fidelity_le_fidelity_traceRight
