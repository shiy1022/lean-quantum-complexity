import QIP.Gen.Model

/-! Fresh-import audit for the Q30 groundwork (unitary provers, generalized provers):
statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix

#check (accept_dilateU : ∀ {d : Desc} (T : IsoStrategy (Reg d) (Reg d) d.numMsgs),
  accept (dilateU T).toOp = accept T.toOp)
#check (dilU_mem : ∀ {d : Desc} (T : IsoStrategy (Reg d) (Reg d) d.numMsgs) {k : ℕ},
  dilU T k ∈ Matrix.unitaryGroup (Reg d k × DilMem d T) ℂ)
#check (gAcc_le_value : ∀ {d : Desc} (G : GProver d) (ξ₀ : Qubits d.totalWires × G.N → ℂ),
  d.Valid → GInit d ξ₀ → gAcc G ξ₀ ≤ value d)

#print axioms ShiQIP.exists_unitary_ext
#print axioms ShiQIP.DilMem
#print axioms ShiQIP.ιM
#print axioms ShiQIP.ιM_injective
#print axioms ShiQIP.embM
#print axioms ShiQIP.embM_iso
#print axioms ShiQIP.embV_iso
#print axioms ShiQIP.dilU
#print axioms ShiQIP.dilU_mem
#print axioms ShiQIP.dilU_embM
#print axioms ShiQIP.dilateU
#print axioms ShiQIP.embVec
#print axioms ShiQIP.embVec_ι
#print axioms ShiQIP.embM_mulVec
#print axioms ShiQIP.turnVec_dilateU
#print axioms ShiQIP.mulVec_embSum
#print axioms ShiQIP.pureRun_dilateU
#print axioms ShiQIP.sum_norm_embVec
#print axioms ShiQIP.accept_dilateU
#print axioms ShiQIP.kept
#print axioms ShiQIP.KS
#print axioms ShiQIP.PS
#print axioms ShiQIP.gsplit
#print axioms ShiQIP.GProver
#print axioms ShiQIP.gturn
#print axioms ShiQIP.gRun
#print axioms ShiQIP.gAcc
#print axioms ShiQIP.GInit
#print axioms ShiQIP.tv
#print axioms ShiQIP.tv_apply
#print axioms ShiQIP.tv_submatrix
#print axioms ShiQIP.tv_mul
#print axioms ShiQIP.pmat
#print axioms ShiQIP.pmat_refl
#print axioms ShiQIP.pmat_iso
#print axioms ShiQIP.tv_pmat
#print axioms ShiQIP.mergeP
#print axioms ShiQIP.form
#print axioms ShiQIP.regSet_self
#print axioms ShiQIP.σswap
#print axioms ShiQIP.regSet_apply'
#print axioms ShiQIP.tv_swap_form
#print axioms ShiQIP.gsplit_symm_apply
#print axioms ShiQIP.gsplit_apply
#print axioms ShiQIP.UL
#print axioms ShiQIP.tv_UL
#print axioms ShiQIP.kronU_iso
#print axioms ShiQIP.UL_iso
#print axioms ShiQIP.σin
#print axioms ShiQIP.σout
#print axioms ShiQIP.simV
#print axioms ShiQIP.simV_iso
#print axioms ShiQIP.held_succ_iff_of_not_reg
#print axioms ShiQIP.not_priv_of_inReg
#print axioms ShiQIP.held_reg_toP
#print axioms ShiQIP.held_reg_toV
#print axioms ShiQIP.kept_iff_toP
#print axioms ShiQIP.kept_iff_held_succ_toP
#print axioms ShiQIP.kept_iff_held_toV
#print axioms ShiQIP.held_succ_iff_toV
#print axioms ShiQIP.form_congr
#print axioms ShiQIP.tv_one
#print axioms ShiQIP.block_form
#print axioms ShiQIP.sum_form_merge
#print axioms ShiQIP.simT
#print axioms ShiQIP.turnVec_simT
#print axioms ShiQIP.init_form
#print axioms ShiQIP.pureRun_simT
#print axioms ShiQIP.outBit_mergeP
#print axioms ShiQIP.gAcc_le_value
