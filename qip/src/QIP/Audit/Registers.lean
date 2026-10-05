import Quantum.Reindex

/-! Fresh-import audit for Q02: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped Kronecker

#check (card_qubits_zero : Fintype.card (Qubits 0) = 1)
#check (regSwap_trans_regSwap : ∀ (α β : Type), (regSwap α β).trans (regSwap β α) = Equiv.refl _)
#check (qubitsAppend_zero_right : ∀ {n : ℕ} (a : Qubits n) (b : Qubits 0),
  qubitsAppend n 0 (a, b) = a)
#check (permMat_conj : ∀ {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β] (e : α ≃ β)
  (M : Matrix α α ℂ), permMat e * M * (permMat e)ᴴ = Matrix.reindex e e M)
#check (kron_regAssoc : ∀ {α β γ α' β' γ' : Type} (A : Matrix α α' ℂ) (B : Matrix β β' ℂ)
  (C : Matrix γ γ' ℂ),
  Matrix.reindex (regAssoc α β γ) (regAssoc α' β' γ') (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C))
#check (kron_regUnitRight : ∀ {α α' : Type} (A : Matrix α α' ℂ),
  Matrix.reindex (regUnitRight α) (regUnitRight α') (A ⊗ₖ (1 : Matrix Unit Unit ℂ)) = A)

#print axioms ShiQuantum.card_qubits
#print axioms ShiQuantum.card_qubits_zero
#print axioms ShiQuantum.regAssoc_symm_trans
#print axioms ShiQuantum.regAssoc_trans_symm
#print axioms ShiQuantum.regSwap_trans_regSwap
#print axioms ShiQuantum.regUnitRight_symm_trans
#print axioms ShiQuantum.regUnitRight_trans_symm
#print axioms ShiQuantum.qubitsAppend_zero_right
#print axioms ShiQuantum.qubitsAppend_zero_left
#print axioms ShiQuantum.qubitsAppend_zero_right_eq
#print axioms ShiQuantum.qubitsAppend_assoc
#print axioms ShiQuantum.reindexState_symm_self
#print axioms ShiQuantum.reindexState_inner
#print axioms ShiQuantum.permMat_mulVec
#print axioms ShiQuantum.permMat_refl
#print axioms ShiQuantum.permMat_trans
#print axioms ShiQuantum.permMat_conjTranspose
#print axioms ShiQuantum.permMat_mul_symm
#print axioms ShiQuantum.permMat_conjTranspose_mul
#print axioms ShiQuantum.permMat_mul_conjTranspose
#print axioms ShiQuantum.permMat_conj
#print axioms ShiQuantum.tensorState_assoc
#print axioms ShiQuantum.tensorState_swap
#print axioms ShiQuantum.tensorState_unitRight
#print axioms ShiQuantum.kron_regAssoc
#print axioms ShiQuantum.kron_regSwap
#print axioms ShiQuantum.reindex_regSwap_twice
#print axioms ShiQuantum.kron_regUnitRight
#print axioms ShiQuantum.permMat_prodCongr
