import QIP.StrategyOperator

/-! Fresh-import audit for Q18: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix
open scoped ComplexOrder

#check (IsStrategy.trace_eq : ∀ {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] {r : ℕ}
  {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ}, IsStrategy r Q →
  ∀ k ≤ r, trace (Q k) = ∏ i ∈ Finset.range k, (Fintype.card (X i) : ℂ))
#check (isStrategy_one_iff_choi : ∀ {X Y : ℕ → Type} [∀ i, Fintype (X i)]
  [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]
  (Φ : MatMap (X 0) (Y 0)), IsStrategy 1 (oneTurn (X := X) (Y := Y) (choi Φ)) ↔ IsChannel Φ)

#print axioms ShiQIP.IsStrategy.trace_eq
#print axioms ShiQIP.kronecker_one_injective
#print axioms ShiQIP.IsStrategy.prefix_unique
#print axioms ShiQIP.isStrategy_one_iff
#print axioms ShiQIP.isStrategy_one_iff_choi
#print axioms ShiQIP.isStrategy_one_prep_iff
