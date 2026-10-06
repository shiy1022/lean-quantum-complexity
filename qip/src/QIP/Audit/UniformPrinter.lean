import QIP.Uniform.ThreePT

/-! Fresh-import audit for Q35-Q38 (the description transformers are polynomial time, uniform
compression and repetition, the printer): statement types, then transitive axioms. -/

open ShiQIP ShiQIP.Uniform ShiQIP.Arith

#check (compG_eq : ∀ (r : ℕ) {d : Desc}, d.Valid → d.HasSchedule (padM r) → compG d = compressR r d)
#check (threeG_eq : ∀ {d : Desc}, d.Valid → threeG d = threeDesc d)
#check (printer_encode : ∀ {d : Desc}, d.Valid → printer (encode d) = encode (threeDesc d))
#check (printer_polyTime : PvsNP.PolyTimeComputable printer)

#print axioms ShiQIP.Uniform.PT.fp_pairMsgs
#print axioms ShiQIP.Uniform.PT.fp_segs
#print axioms ShiQIP.Uniform.PT.fp_pos₁
#print axioms ShiQIP.Uniform.PT.fp_pos₂
#print axioms ShiQIP.Uniform.PT.fp_pairBlock
#print axioms ShiQIP.Uniform.PT.fp_pairDesc
#print axioms ShiQIP.Uniform.PT.fp_flagWidths
#print axioms ShiQIP.Uniform.PT.fp_flagMsgs
#print axioms ShiQIP.Uniform.PT.fp_flagDesc
#print axioms ShiQIP.Uniform.PT.fp_rejectDesc
#print axioms ShiQIP.Uniform.decide_lastToVerifier
#print axioms ShiQIP.Uniform.PT.fp_lastToVerifier
#print axioms ShiQIP.Uniform.PT.fp_appendV
#print axioms ShiQIP.Uniform.PT.fp_normDesc
#print axioms ShiQIP.Uniform.PT.fp_bellShift
#print axioms ShiQIP.Uniform.PT.fp_swapAll
#print axioms ShiQIP.Uniform.PT.fp_bellFinal
#print axioms ShiQIP.Uniform.PT.fp_bellBlock
#print axioms ShiQIP.Uniform.PT.fp_bellDesc
#print axioms ShiQIP.Uniform.PT.fp_perfDesc
#print axioms ShiQIP.Uniform.foldS_append
#print axioms ShiQIP.Uniform.padStep
#print axioms ShiQIP.Uniform.padRun
#print axioms ShiQIP.Uniform.padM_succ'
#print axioms ShiQIP.Uniform.padExp_le
#print axioms ShiQIP.Uniform.padRun_pre
#print axioms ShiQIP.Uniform.padRun_post
#print axioms ShiQIP.Uniform.padRun_eq
#print axioms ShiQIP.Uniform.padM_padExp_le
#print axioms ShiQIP.Uniform.PT.padRunU
#print axioms ShiQIP.Uniform.PT.fp_padExp
#print axioms ShiQIP.Uniform.PT.fp_padCount
#print axioms ShiQIP.Uniform.PT.fp_dummyMsgs
#print axioms ShiQIP.Uniform.PT.fp_padDesc
#print axioms ShiQIP.Uniform.PT.fp_padTo
#print axioms ShiQIP.Uniform.PT.fp_wd
#print axioms ShiQIP.Uniform.PT.fp_hw
#print axioms ShiQIP.Uniform.PT.fp_held0
#print axioms ShiQIP.Uniform.PT.fp_hAnc
#print axioms ShiQIP.Uniform.PT.fp_hPriv
#print axioms ShiQIP.Uniform.PT.fp_hMsgs
#print axioms ShiQIP.Uniform.PT.fp_hOff
#print axioms ShiQIP.Uniform.PT.fp_hPay
#print axioms ShiQIP.Uniform.PT.fp_swapMsg
#print axioms ShiQIP.Uniform.PT.fp_onF
#print axioms ShiQIP.Uniform.PT.fp_onB
#print axioms ShiQIP.Uniform.PT.fp_fwdStep
#print axioms ShiQIP.Uniform.PT.fp_bwdStep
#print axioms ShiQIP.Uniform.PT.fp_hBlock
#print axioms ShiQIP.Uniform.PT.fp_halveDesc
#print axioms ShiQIP.Uniform.enc_list_length
#print axioms ShiQIP.Uniform.enc_desc_length
#print axioms ShiQIP.Uniform.enc_msg_length
#print axioms ShiQIP.Uniform.enc_gate_bounds
#print axioms ShiQIP.Uniform.sum_map_le_sum_map
#print axioms ShiQIP.Uniform.sum_two_encLen
#print axioms ShiQIP.Uniform.sum_width_add_length
#print axioms ShiQIP.Uniform.serialSize_le_enc
#print axioms ShiQIP.Uniform.enc_le_serialSize
#print axioms ShiQIP.Uniform.hsize_le_enc
#print axioms ShiQIP.Uniform.enc_le_hsize
#print axioms ShiQIP.Uniform.hGuard
#print axioms ShiQIP.Uniform.gHalve
#print axioms ShiQIP.Uniform.PT.gHalveU
#print axioms ShiQIP.Uniform.pwStep
#print axioms ShiQIP.Uniform.pw
#print axioms ShiQIP.Uniform.powList
#print axioms ShiQIP.Uniform.pw_pre
#print axioms ShiQIP.Uniform.pw_post
#print axioms ShiQIP.Uniform.pw_padM
#print axioms ShiQIP.Uniform.compG
#print axioms ShiQIP.Uniform.foldS_gHalve_powList
#print axioms ShiQIP.Uniform.compG_eq
#print axioms ShiQIP.Uniform.pw_inv
#print axioms ShiQIP.Uniform.pw_length
#print axioms ShiQIP.Uniform.PT.pwU
#print axioms ShiQIP.Uniform.PT.fp_pw
#print axioms ShiQIP.Uniform.gHalve_bound
#print axioms ShiQIP.Uniform.numMsgs_le_enc
#print axioms ShiQIP.Uniform.PT.compGU
#print axioms ShiQIP.Uniform.PT.fp_compG
#print axioms ShiQIP.Uniform.rStep
#print axioms ShiQIP.Uniform.repG
#print axioms ShiQIP.Uniform.foldS_rStep_valid
#print axioms ShiQIP.Uniform.foldS_rStep_invalid
#print axioms ShiQIP.Uniform.repG_eq
#print axioms ShiQIP.Uniform.hsize_repeatAux_le
#print axioms ShiQIP.Uniform.PT.repGU
#print axioms ShiQIP.Uniform.PT.fp_repG
#print axioms ShiQIP.Uniform.threeG
#print axioms ShiQIP.Uniform.PT.fp_sq
#print axioms ShiQIP.Uniform.PT.fp_repK
#print axioms ShiQIP.Uniform.PT.threeGU
#print axioms ShiQIP.Uniform.padStage_spec
#print axioms ShiQIP.Uniform.threeG_eq
#print axioms ShiQIP.Uniform.printer
#print axioms ShiQIP.Uniform.printer_encode
#print axioms ShiQIP.Uniform.PT.printerU
#print axioms ShiQIP.Uniform.printer_polyTime
