import QIP.Circuit.Controlled

/-! Fresh-import audit for Q28 (controlled circuits): exact statement types, then axioms. -/

open ShiQIP ShiQuantum Matrix ShiShallow

#check (runLayer_ctrlInstrs : ∀ {n : ℕ} {c a : Fin n}, c ≠ a → ∀ (l : List (Instr n)),
  (∀ g ∈ l, c ∉ g.support ∧ a ∉ g.support) → ∀ {ψ : QState n}, Clean a ψ → ∀ y,
    runLayer (ctrlInstrs c a l) ψ y = if y c then runLayer l ψ y else ψ y)
#check (clean_ctrlInstrs : ∀ {n : ℕ} {c a : Fin n}, c ≠ a → ∀ (l : List (Instr n)),
  (∀ g ∈ l, c ∉ g.support ∧ a ∉ g.support) → ∀ {ψ : QState n}, Clean a ψ →
    Clean a (runLayer (ctrlInstrs c a l) ψ))
#check (filterMap_ctrlGates : ∀ {N : ℕ} (c a : Fin N), c ≠ a → ∀ (gs : List Gate),
  (∀ g ∈ gs, (g.toInstr? N).isSome ∧ (c : ℕ) ∉ g.wires ∧ (a : ℕ) ∉ g.wires) →
    (ctrlGates c a gs).filterMap (Gate.toInstr? N) =
      ctrlInstrs c a (gs.filterMap (Gate.toInstr? N)))
#check (length_ctrlGates_le : ∀ (c a : ℕ) (gs : List Gate),
  (ctrlGates c a gs).length ≤ 67 * gs.length)

#print axioms ShiQIP.SliceEq
#print axioms ShiQIP.Clean
#print axioms ShiQIP.apply1_sliceEq
#print axioms ShiQIP.instr_apply_sliceEq
#print axioms ShiQIP.runLayer_nil
#print axioms ShiQIP.runLayer_cons
#print axioms ShiQIP.runLayer_sliceEq
#print axioms ShiQIP.instr_apply_zero
#print axioms ShiQIP.Clean.apply
#print axioms ShiQIP.sdg
#print axioms ShiQIP.ctrlInstr
#print axioms ShiQIP.apply_s
#print axioms ShiQIP.runLayer_toffoli'
#print axioms ShiQIP.runLayer_ctrl_x
#print axioms ShiQIP.runLayer_ctrl_cnot
#print axioms ShiQIP.runLayer_ctrl_s
#print axioms ShiQIP.runLayer_ctrl_t
#print axioms ShiQIP.apply1_apply1
#print axioms ShiQIP.apply1_one
#print axioms ShiQIP.runLayer_tdg
#print axioms ShiQIP.runLayer_sdg
#print axioms ShiQIP.tPhase_eq
#print axioms ShiQIP.sht_x_sht_dag
#print axioms ShiQIP.sht_unitary
#print axioms ShiQIP.runLayer_ctrl_h
#print axioms ShiQIP.ctrlInstrs
#print axioms ShiQIP.runLayer_ctrlInstr
#print axioms ShiQIP.Clean.runLayer
#print axioms ShiQIP.runLayer_ctrlInstrs
#print axioms ShiQIP.clean_ctrlInstrs
#print axioms ShiQIP.length_toffoliInstrs
#print axioms ShiQIP.length_ctrlInstr_le
#print axioms ShiQIP.length_ctrlInstrs_le
#print axioms ShiQIP.sdgGates
#print axioms ShiQIP.ctrlGate
#print axioms ShiQIP.ctrlGates
#print axioms ShiQIP.length_ctrlGates_le
#print axioms ShiQIP.mem_support_of_toInstr?
#print axioms ShiQIP.filterMap_ctrlGate
#print axioms ShiQIP.filterMap_ctrlGates
