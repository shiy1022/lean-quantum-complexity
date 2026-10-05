import QIP.GateMatrix

/-! Fresh-import audit for the Q16 gate-matrix groundwork: exact statement types, axioms. -/

open ShiQIP ShiQuantum Matrix ShiShallow

#check (instrMat_mulVec : ∀ {n : ℕ} (g : Instr n) (ψ : QState n), instrMat g *ᵥ ψ = g.apply ψ)
#check (instrMat_mem_unitaryGroup : ∀ {n : ℕ} (g : Instr n),
  instrMat g ∈ Matrix.unitaryGroup (Bits n) ℂ)
#check (conjMap_instr_pureState : ∀ {n : ℕ} (g : Instr n) (ψ : QState n),
  conjMap (instrMat g) (pureState ψ) = pureState (g.apply ψ))

#print axioms ShiQIP.splitAt_symm_apply
#print axioms ShiQIP.oneQubitMat_mulVec
#print axioms ShiQIP.cnotFun_involutive
#print axioms ShiQIP.cnotMat_mulVec
#print axioms ShiQIP.instrMat_mulVec
#print axioms ShiQIP.oneQubitMat_mem_unitaryGroup
#print axioms ShiQIP.cnotMat_mem_unitaryGroup
#print axioms ShiQIP.hMat_mem_unitaryGroup
#print axioms ShiQIP.sMat_mem_unitaryGroup
#print axioms ShiQIP.tMat_mem_unitaryGroup
#print axioms ShiQIP.xMat_mem_unitaryGroup
#print axioms ShiQIP.instrMat_mem_unitaryGroup
#print axioms ShiQIP.isChannel_instr
#print axioms ShiQIP.conjMap_instr_pureState
