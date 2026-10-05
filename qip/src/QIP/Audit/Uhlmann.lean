import Quantum.Uhlmann

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
