import Quantum.PartialTrace

/-! Fresh-import audit for Q05: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder Kronecker

#check (traceRight_apply : ∀ {α α' β : Type} [Fintype β] (M : Matrix (α × β) (α' × β) ℂ)
  (a : α) (b : α'), traceRight M a b = ∑ i, M (a, i) (b, i))
#check (posSemidef_traceRight : ∀ {α β : Type} [Fintype α] [Fintype β]
  {M : Matrix (α × β) (α × β) ℂ}, M.PosSemidef → (traceRight M).PosSemidef)
#check (trace_traceRight : ∀ {α β : Type} [Fintype α] [Fintype β]
  (M : Matrix (α × β) (α × β) ℂ), trace (traceRight M) = trace M)
#check (traceRight_kronecker : ∀ {α α' β : Type} [Fintype β] (A : Matrix α α' ℂ)
  (B : Matrix β β ℂ), traceRight (A ⊗ₖ B) = trace B • A)
#check (traceRight_conj_unitary : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β] {U : Matrix β β ℂ}, U ∈ Matrix.unitaryGroup β ℂ →
  ∀ M : Matrix (α × β) (α × β) ℂ,
  traceRight (((1 : Matrix α α ℂ) ⊗ₖ U) * M * ((1 : Matrix α α ℂ) ⊗ₖ U)ᴴ) = traceRight M)
#check (trace_mul_traceRight : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
  (A : Matrix α α ℂ) (M : Matrix (α × β) (α × β) ℂ),
  trace (A * traceRight M) = trace ((A ⊗ₖ (1 : Matrix β β ℂ)) * M))
#check (traceRight_bell : traceRight (pureState bellVec) = maxMixed Bool)

#print axioms ShiQuantum.traceRight_add
#print axioms ShiQuantum.traceRight_smul
#print axioms ShiQuantum.traceRight_sub
#print axioms ShiQuantum.trace_traceRight
#print axioms ShiQuantum.trace_traceLeft
#print axioms ShiQuantum.traceRight_conjTranspose
#print axioms ShiQuantum.traceRight_eq_sum_slice
#print axioms ShiQuantum.posSemidef_traceRight
#print axioms ShiQuantum.IsDensity.traceRight
#print axioms ShiQuantum.traceLeft_eq_traceRight_swap
#print axioms ShiQuantum.posSemidef_traceLeft
#print axioms ShiQuantum.IsDensity.traceLeft
#print axioms ShiQuantum.traceRight_kronecker
#print axioms ShiQuantum.traceLeft_kronecker
#print axioms ShiQuantum.IsDensity.kronecker
#print axioms ShiQuantum.traceRight_product
#print axioms ShiQuantum.traceLeft_product
#print axioms ShiQuantum.traceRight_local
#print axioms ShiQuantum.traceRight_mul_one_kronecker_comm
#print axioms ShiQuantum.traceRight_conj_unitary
#print axioms ShiQuantum.trace_mul_traceRight
#print axioms ShiQuantum.traceRight_reindex_left
#print axioms ShiQuantum.traceRight_reindex_right
#print axioms ShiQuantum.traceRight_prod
#print axioms ShiQuantum.traceRight_unique
#print axioms ShiQuantum.traceRight_unitRight
#print axioms ShiQuantum.invSqrtTwo_mul_star
#print axioms ShiQuantum.traceRight_bell
#print axioms ShiQuantum.isDensity_bell
#print axioms ShiQuantum.traceRight_bell_not_pure
