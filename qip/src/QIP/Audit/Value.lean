import QIP.Value

/-! Fresh-import audit for Q21: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix
open scoped ComplexOrder

#check (exists_optimal_prover : ∀ d : Desc, ∃ Pstar : Prover d, ∀ P : Prover d,
  accept P ≤ accept Pstar)
#check (value_attained : ∀ d : Desc, ∃ Pstar : Prover d, accept Pstar = value d)
#check (value_mem_Icc : ∀ d : Desc, value d ∈ Set.Icc 0 1)
#check (le_value_iff : ∀ (d : Desc) (c : ℝ), (∃ P : Prover d, c ≤ accept P) ↔ c ≤ value d)
#check (value_le_iff : ∀ (d : Desc) (s : ℝ), (∀ P : Prover d, accept P ≤ s) ↔ value d ≤ s)
#check (exists_accept_eq_one_of_value_eq_one : ∀ d : Desc, value d = 1 →
  ∃ P : Prover d, accept P = 1)
#check (isCompact_feasible : ∀ d : Desc, IsCompact (feasible d))

#print axioms ShiQIP.norm_apply_le_trace
#print axioms ShiQIP.isClosed_nonneg_complex
#print axioms ShiQIP.isClosed_posSemidef
#print axioms ShiQIP.continuous_traceRight
#print axioms ShiQIP.continuous_kronecker_one
#print axioms ShiQIP.isStrategy_congr
#print axioms ShiQIP.proverFam_mem
#print axioms ShiQIP.isClosed_feasible
#print axioms ShiQIP.isCompact_entryBox
#print axioms ShiQIP.isCompact_box
#print axioms ShiQIP.feasible_subset_box
#print axioms ShiQIP.isCompact_feasible
#print axioms ShiQIP.continuous_pairing
#print axioms ShiQIP.accept_eq_pairing_fam
#print axioms ShiQIP.exists_optimal_prover
#print axioms ShiQIP.value_attained
#print axioms ShiQIP.accept_le_value
#print axioms ShiQIP.value_mem_Icc
#print axioms ShiQIP.le_value_iff
#print axioms ShiQIP.value_le_iff
#print axioms ShiQIP.exists_accept_eq_one_of_value_eq_one
