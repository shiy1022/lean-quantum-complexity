import Quantum.FidelityTwoTargets

/-! Fresh-import audit for Q12: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped InnerProductSpace

#check (two_overlaps_le : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {u v w : V}, ‖u‖ = 1 → ‖v‖ = 1 → ‖w‖ = 1 →
  ‖⟪w, u⟫_ℂ‖ ^ 2 + ‖⟪w, v⟫_ℂ‖ ^ 2 ≤ 1 + ‖⟪u, v⟫_ℂ‖)
#check (fidelity_two_targets : ∀ {n : Type} [Fintype n] [DecidableEq n]
  {ρ σ τ : Matrix n n ℂ}, IsDensity ρ → IsDensity σ → IsDensity τ →
  fidelity ρ σ ^ 2 + fidelity ρ τ ^ 2 ≤ 1 + fidelity σ τ)

#print axioms ShiQuantum.two_overlaps_le
#print axioms ShiQuantum.norm_toE_eq_one_of_purification
#print axioms ShiQuantum.fidelity_two_targets
