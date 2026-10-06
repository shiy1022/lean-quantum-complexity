import QIP.StrategyRealize

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

/-! Operational strategies (Q19 forward direction). -/

#check (opStrategy_isStrategy : ∀ {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] {r : ℕ} (S : OpStrategy X Y r),
  IsStrategy r (stratOp S))

#print axioms ShiQIP.linkStep_posSemidef
#print axioms ShiQIP.traceRight_link
#print axioms ShiQIP.traceRight_linkStep
#print axioms ShiQIP.memState_posSemidef
#print axioms ShiQIP.stratOp_succ
#print axioms ShiQIP.opStrategy_isStrategy

/-! Realization (Q19 reverse direction). -/

#check (exists_opStrategy_of_isStrategy : ∀ {X Y : ℕ → Type} [∀ i, Fintype (X i)]
  [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] [∀ i, Nonempty (X i)]
  [∀ i, Nonempty (Y i)] {r : ℕ} {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ},
  IsStrategy r Q → ∃ S : OpStrategy X Y r, (∀ k, S.M k = Hist X Y k) ∧ ∀ k ≤ r, stratOp S k = Q k)
#check (isStrategy_iff_realized : ∀ {X Y : ℕ → Type} [∀ i, Fintype (X i)]
  [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] [∀ i, Nonempty (X i)]
  [∀ i, Nonempty (Y i)] {r : ℕ} (Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ),
  IsStrategy r Q ↔ ∃ S : OpStrategy X Y r, ∀ k ≤ r, stratOp S k = Q k)

#print axioms ShiQuantum.kronecker_pureState
#print axioms ShiQuantum.reindex_pureState
#print axioms ShiQuantum.liftR_conjMap_pureState
#print axioms ShiQuantum.liftR_sum
#print axioms ShiQuantum.completeKraus_sum
#print axioms ShiQuantum.isChannel_completeKraus
#print axioms ShiQuantum.completeKraus_some_mulVec
#print axioms ShiQuantum.liftR_completeKraus_pureState
#print axioms ShiQIP.exists_contraction_relating
#print axioms ShiQIP.transpose_contraction
#print axioms ShiQIP.pureState_linkVec
#print axioms ShiQIP.isPurification_linkVec
#print axioms ShiQIP.exists_turn
#print axioms ShiQIP.memState_realize
#print axioms ShiQIP.exists_opStrategy_of_isStrategy
#print axioms ShiQIP.isStrategy_iff_realized
