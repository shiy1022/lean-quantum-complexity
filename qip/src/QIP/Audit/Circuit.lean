import QIP.Circuit.Toffoli

/-! Fresh-import audit for Q28 (adjoints and swap): exact statement types, then axioms. -/

open ShiQIP ShiQuantum Matrix ShiShallow

#check (layerMat_adjointInstrs : ∀ {n : ℕ} (l : List (Instr n)),
  layerMat (adjointInstrs l) = (layerMat l)ᴴ)
#check (runLayer_adjointInstrs : ∀ {n : ℕ} (l : List (Instr n)) (ψ : QState n),
  runLayer (adjointInstrs l) (runLayer l ψ) = ψ)
#check (length_adjointGates_le : ∀ l : List Gate, (adjointGates l).length ≤ 7 * l.length)
#check (runLayer_swapInstrs : ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n),
  runLayer (swapInstrs i j hij) ψ = fun y => ψ (y ∘ Equiv.swap i j))

#print axioms ShiQIP.oneQubitMat_mul
#print axioms ShiQIP.oneQubitMat_conjTranspose
#print axioms ShiQIP.hMat_conjTranspose
#print axioms ShiQIP.xMat_conjTranspose
#print axioms ShiQIP.sMat_cube
#print axioms ShiQIP.tPhase_pow_eight
#print axioms ShiQIP.tPhase_pow_seven
#print axioms ShiQIP.tMat_pow_seven
#print axioms ShiQIP.foldl_instrMat_eq
#print axioms ShiQIP.layerMat_cons
#print axioms ShiQIP.layerMat_append
#print axioms ShiQIP.cnotMat_conjTranspose
#print axioms ShiQIP.layerMat_instrInv
#print axioms ShiQIP.layerMat_adjointInstrs
#print axioms ShiQIP.runLayer_adjointInstrs
#print axioms ShiQIP.length_adjointInstrs_le
#print axioms ShiQIP.length_adjointGates_le
#print axioms ShiQIP.filterMap_inv
#print axioms ShiQIP.filterMap_adjointGates
#print axioms ShiQIP.cnot_cnot_cnot
#print axioms ShiQIP.runLayer_swapInstrs
#print axioms ShiQIP.swapInstrs_mulVec
#print axioms ShiQIP.filterMap_swapGates

/-! Toffoli. -/

#check (runLayer_ccz : ∀ {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (ψ : QState n) (y : Bits n), runLayer (cczInstrs a b c hab hac hbc) ψ y =
    (if y a && y b && y c then -1 else 1) * ψ y)
#check (runLayer_toffoli : ∀ {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (ψ : QState n) (y : Bits n), runLayer (toffoliInstrs a b c hab hac hbc) ψ y =
    ψ (Function.update y c (xor (y c) (y a && y b))))

#print axioms ShiQIP.update_of_eq
#print axioms ShiQIP.apply_t
#print axioms ShiQIP.tPhase_pow_four
#print axioms ShiQIP.pow_eq_pow_mod_eight
#print axioms ShiQIP.runLayer_ccz
#print axioms ShiQIP.apply_h
#print axioms ShiQIP.runLayer_toffoli
#print axioms ShiQIP.toffoli_controls_preserved
#print axioms ShiQIP.length_toffoliGates
#print axioms ShiQIP.filterMap_toffoliGates
