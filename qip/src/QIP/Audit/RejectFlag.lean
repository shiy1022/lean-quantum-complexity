import QIP.RejectFlag

/-! Fresh-import audit for Q26: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix

#check (value_rejectDesc : ∀ {d : Desc}, d.Valid → 1 ≤ d.numMsgs → LastToVerifier d →
  value (rejectDesc d) = value d)
#check (exists_accept_rejectDesc : ∀ {d : Desc}, d.Valid → 1 ≤ d.numMsgs → LastToVerifier d →
  ∀ {t : ℝ}, 0 ≤ t → t ≤ value d → ∃ P : Prover (rejectDesc d), accept P = t)
#check (exists_accept_half : ∀ {d : Desc}, d.Valid → 1 ≤ d.numMsgs → LastToVerifier d →
  (1 : ℝ) / 2 ≤ value d → ∃ P : Prover (rejectDesc d), accept P = 1 / 2)
#check (rejectDesc_valid : ∀ {d : Desc}, d.Valid → 1 ≤ d.numMsgs → LastToVerifier d →
  (rejectDesc d).Valid)

#print axioms ShiQIP.histMap_symm_apply
#print axioms ShiQIP.PairData.exists_accept_mul
#print axioms ShiQIP.nonAdaptive
#print axioms ShiQIP.nonAdaptive_posSemidef
#print axioms ShiQIP.nonAdaptive_isStrategy
#print axioms ShiQIP.flagWidths
#print axioms ShiQIP.flagMsgs
#print axioms ShiQIP.flagDesc
#print axioms ShiQIP.length_flagWidths
#print axioms ShiQIP.zipWith_widths
#print axioms ShiQIP.zipWith_dirs
#print axioms ShiQIP.flagMsgs_widths
#print axioms ShiQIP.flagMsgs_dirs
#print axioms ShiQIP.numMsgs_flagDesc
#print axioms ShiQIP.totalWires_flagDesc
#print axioms ShiQIP.psum_flagWidths
#print axioms ShiQIP.getD_flagWidths
#print axioms ShiQIP.inReg_flagDesc
#print axioms ShiQIP.oW
#print axioms ShiQIP.fW
#print axioms ShiQIP.oW_ne_fW
#print axioms ShiQIP.fin_flag
#print axioms ShiQIP.qubits_flag_ext
#print axioms ShiQIP.not_inReg_oW
#print axioms ShiQIP.isEmpty_reg_flag
#print axioms ShiQIP.subsingleton_reg_flag
#print axioms ShiQIP.fSub
#print axioms ShiQIP.eq_fSub
#print axioms ShiQIP.reg_flag_ext
#print axioms ShiQIP.blocks_flag_getD
#print axioms ShiQIP.blockMat_flag_lt
#print axioms ShiQIP.blockMat_flag_last
#print axioms ShiQIP.transMat_flag
#print axioms ShiQIP.cnotMat_mul_apply
#print axioms ShiQIP.transMat_flag_last
#print axioms ShiQIP.subsingleton_hist_flag
#print axioms ShiQIP.histZero
#print axioms ShiQIP.hAcc
#print axioms ShiQIP.lastIn
#print axioms ShiQIP.lastOut
#print axioms ShiQIP.testerAt_flag
#print axioms ShiQIP.pairing_flag
#print axioms ShiQIP.flagSigma
#print axioms ShiQIP.flagSigma_isDensity
#print axioms ShiQIP.nonAdaptive_flag_zero
#print axioms ShiQIP.pairing_flagSigma
#print axioms ShiQIP.value_flagDesc
#print axioms ShiQIP.LastToVerifier
#print axioms ShiQIP.flagDesc_valid
#print axioms ShiQIP.rejectDesc
#print axioms ShiQIP.rejectDesc_valid
#print axioms ShiQIP.numMsgs_rejectDesc
#print axioms ShiQIP.schedule_rejectDesc
#print axioms ShiQIP.value_rejectDesc
#print axioms ShiQIP.exists_accept_rejectDesc
#print axioms ShiQIP.exists_accept_half
#print axioms ShiQIP.lastToVerifier_of_hasSchedule
