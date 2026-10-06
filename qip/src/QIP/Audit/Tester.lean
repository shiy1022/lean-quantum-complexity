import QIP.Tester

/-! Fresh-import audit for Q20: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix
open scoped ComplexOrder Kronecker

#check (accept_eq_pairing : ∀ {d : Desc} (P : Prover d),
  accept P = (trace (tester d * stratOp P d.numMsgs)).re)
#check (tester_posSemidef : ∀ d : Desc, (tester d).PosSemidef)
#check (pairing_mem_Icc : ∀ {d : Desc}
  {Q : ∀ k, Matrix (Hist (Reg d) (Reg d) k) (Hist (Reg d) (Reg d) k) ℂ},
  IsStrategy d.numMsgs Q → (trace (tester d * Q d.numMsgs)).re ∈ Set.Icc 0 1)
#check (stateAfterBlock_eq : ∀ {d : Desc} (P : Prover d), ∀ j ≤ d.numMsgs,
  stateAfterBlock P j = (transMat d j ⊗ₖ (1 : Matrix (P.M j) (P.M j) ℂ)) * memState P j *
    (transMat d j ⊗ₖ (1 : Matrix (P.M j) (P.M j) ℂ))ᴴ)

#print axioms ShiQIP.linkStep_apply
#print axioms ShiQIP.star_ite_zero
#print axioms ShiQIP.kron_one_apply
#print axioms ShiQIP.conjKron_apply
#print axioms ShiQIP.blockOf_expand
#print axioms ShiQIP.sum_transfer_left
#print axioms ShiQIP.sum_transfer_right
#print axioms ShiQIP.turn_conj
#print axioms ShiQIP.proverStep_eq_turnMap
#print axioms ShiQIP.tester_posSemidef
#print axioms ShiQIP.conj_kron_one_mul
#print axioms ShiQIP.conjMap_pureState
#print axioms ShiQIP.stateAfterBlock_eq
#print axioms ShiQIP.accept_eq_pairing
#print axioms ShiQIP.pairing_mem_Icc
