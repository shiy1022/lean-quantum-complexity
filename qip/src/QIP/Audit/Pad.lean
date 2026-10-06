import QIP.PadMessages

/-! Fresh-import audit for Q29 (message padding): statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix

#check (value_padDesc : ∀ {d : Desc} {s : ℕ}, value (padDesc d s) = value d)
#check (padDesc_valid : ∀ {d : Desc} {s : ℕ}, d.Valid → ∀ {m : ℕ}, d.HasSchedule m →
  (padDesc d s).Valid)
#check (hasSchedule_padDesc : ∀ {d : Desc} {s m : ℕ}, d.HasSchedule m →
  (padDesc d s).HasSchedule (m + s))
#check (exists_accept_padDesc : ∀ {d : Desc} {s : ℕ} (P : Prover d),
  ∃ P' : Prover (padDesc d s), accept P' = accept P)
#check (hasSchedule_padTo : ∀ {d : Desc} {m : ℕ}, d.HasSchedule m →
  (padTo d).HasSchedule (Arith.padCount m))
#check (value_padTo : ∀ {d : Desc}, value (padTo d) = value d)

#print axioms ShiQIP.dummyMsgs
#print axioms ShiQIP.padDesc
#print axioms ShiQIP.length_stdSchedule
#print axioms ShiQIP.length_dummyMsgs
#print axioms ShiQIP.numMsgs_padDesc
#print axioms ShiQIP.width_of_mem_dummyMsgs
#print axioms ShiQIP.width_dummyMsgs
#print axioms ShiQIP.totalWires_padDesc
#print axioms ShiQIP.msgOffset_padDesc
#print axioms ShiQIP.msgWidth_padDesc
#print axioms ShiQIP.msgWidth_padDesc_lt
#print axioms ShiQIP.getElem_stdSchedule
#print axioms ShiQIP.drop_stdSchedule
#print axioms ShiQIP.dirs_padDesc
#print axioms ShiQIP.hasSchedule_padDesc
#print axioms ShiQIP.msgHeld_zero_prefix
#print axioms ShiQIP.msgHeld_shift
#print axioms ShiQIP.msgHeld_shift_zero
#print axioms ShiQIP.held_padDesc
#print axioms ShiQIP.blocks_padDesc_getD
#print axioms ShiQIP.blocks_padDesc_getD_lt
#print axioms ShiQIP.stdSchedule_succ
#print axioms ShiQIP.alternates_canon
#print axioms ShiQIP.alternates_of_dirs
#print axioms ShiQIP.padDesc_valid
#print axioms ShiQIP.eW
#print axioms ShiQIP.eQ
#print axioms ShiQIP.eW_val
#print axioms ShiQIP.eQ_apply
#print axioms ShiQIP.inReg_padDesc
#print axioms ShiQIP.not_inReg_padDesc_lt
#print axioms ShiQIP.τP
#print axioms ShiQIP.layerMat_cast
#print axioms ShiQIP.blockMat_padDesc
#print axioms ShiQIP.blockMat_padDesc_lt
#print axioms ShiQIP.zReg
#print axioms ShiQIP.reg_eq_zero
#print axioms ShiQIP.dummyW
#print axioms ShiQIP.dummyMem
#print axioms ShiQIP.dummyW_iso
#print axioms ShiQIP.isDensity_dummyMem
#print axioms ShiQIP.turnVec_dummy
#print axioms ShiQIP.pureRun_dummy
#print axioms ShiQIP.pureRun_padStart
#print axioms ShiQIP.shiftT
#print axioms ShiQIP.split_τP
#print axioms ShiQIP.regSet_τP
#print axioms ShiQIP.turnVec_shift
#print axioms ShiQIP.zeroVec_eQ
#print axioms ShiQIP.kron_submatrix_mulVec
#print axioms ShiQIP.pureRun_shift
#print axioms ShiQIP.outBit_eQ
#print axioms ShiQIP.accept_shiftT
#print axioms ShiQIP.inReg_padDesc_ge
#print axioms ShiQIP.ρP
#print axioms ShiQIP.mCast
#print axioms ShiQIP.waitV
#print axioms ShiQIP.waitV_iso
#print axioms ShiQIP.waitT
#print axioms ShiQIP.cast_mCast
#print axioms ShiQIP.dummyMem_waitT
#print axioms ShiQIP.V_transport
#print axioms ShiQIP.regCast_apply
#print axioms ShiQIP.shift_waitT_V
#print axioms ShiQIP.accept_waitT
#print axioms ShiQIP.value_padDesc
#print axioms ShiQIP.exists_accept_padDesc
#print axioms ShiQIP.padTo
#print axioms ShiQIP.numMsgs_padTo
#print axioms ShiQIP.hasSchedule_padTo
#print axioms ShiQIP.padTo_valid
#print axioms ShiQIP.value_padTo
#print axioms ShiQIP.totalWires_padTo
#print axioms ShiQIP.exists_accept_padTo
