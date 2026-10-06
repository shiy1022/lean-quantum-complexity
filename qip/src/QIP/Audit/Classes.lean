import QIP.ExecutionLemmas

/-! Fresh-import audit for Q15: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix

#check (QIP : Set PromiseProblem)
#check (QIPm : ℕ → Set PromiseProblem)
example : QIP = {A | ∃ F : VerifierFamily, Decides F A} := rfl
example (k : ℕ) : QIPm k =
    {A | ∃ F : VerifierFamily, (∀ x, (F.desc x).HasSchedule k) ∧ Decides F A} := rfl
example (F : VerifierFamily) (A : PromiseProblem) : Decides F A =
    ((∀ x ∈ A.yes, ∃ P : Prover (F.desc x), (2 : ℝ) / 3 ≤ accept P) ∧
      (∀ x ∈ A.no, ∀ P : Prover (F.desc x), accept P ≤ (1 : ℝ) / 3)) := rfl
#check (qipm_subset_qip : ∀ k : ℕ, QIPm k ⊆ QIP)
#check (accept_mem_Icc : ∀ {d : Desc} (P : Prover d), accept P ∈ Set.Icc 0 1)
#check (proverOwns_private : ∀ {d : Desc} {j w : ℕ}, w < d.priv → d.proverOwns j w = false)
#check (accept_exAlways : ∀ P : Prover exAlways, accept P = 1)
#check (accept_exNever : ∀ P : Prover exNever, accept P = 0)

#print axioms ShiQIP.msgProverOwned_ge
#print axioms ShiQIP.proverOwns_private
#print axioms ShiQIP.isChannel_legalAction
#print axioms ShiQIP.legalAction_marginal
#print axioms ShiQIP.blockMat_mem_unitaryGroup
#print axioms ShiQIP.isChannel_verifierStep
#print axioms ShiQIP.isDensity_zeroVec
#print axioms ShiQIP.isChannel_proverStep
#print axioms ShiQIP.isDensity_initState
#print axioms ShiQIP.isDensity_stateAfterBlock
#print axioms ShiQIP.final_isDensity
#print axioms ShiQIP.isEffect_kronecker_one
#print axioms ShiQIP.isEffect_acceptEffect
#print axioms ShiQIP.accept_mem_Icc
#print axioms ShiQIP.qipm_subset_qip
#print axioms ShiQIP.numMsgs_of_mem_qipm
#print axioms ShiQIP.PromiseProblem.not_yes_and_no
#print axioms ShiQIP.prob_kronecker_one
#print axioms ShiQIP.verifierStep_kronecker
#print axioms ShiQIP.conjMap_layer_pureState
#print axioms ShiQIP.accept_of_numMsgs_eq_zero
#print axioms ShiQIP.sum_qubits_one
#print axioms ShiQIP.outBit_one
#print axioms ShiQIP.accept_exAlways
#print axioms ShiQIP.accept_exNever
