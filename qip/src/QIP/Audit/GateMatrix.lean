import QIP.CircuitSemantics

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

/-! Layered circuits and acceptance. -/

#check (circuitMat_mulVec : ∀ {n : ℕ} (c : Layered n) (ψ : QState n),
  circuitMat c *ᵥ ψ = runLayered c ψ)
#check (acceptProb_eq_prob : ∀ {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)),
  acceptProb c x out = prob (basisEffect fun y : Bits (n + m) => y out = true)
    (conjMap (circuitMat c) (pureState (inputState x))))

#print axioms ShiQIP.foldl_instrMat_mulVec
#print axioms ShiQIP.layerMat_mulVec
#print axioms ShiQIP.circuitMat_mulVec
#print axioms ShiQIP.layerMat_mem_unitaryGroup
#print axioms ShiQIP.circuitMat_mem_unitaryGroup
#print axioms ShiQIP.isChannel_circuit
#print axioms ShiQIP.conjMap_circuit_pureState
#print axioms ShiQIP.acceptProb_eq_prob
