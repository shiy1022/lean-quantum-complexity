import QIP.Halve.Valid

/-! Fresh-import audit for the Q31 halving completeness, validity and schedule: statement types,
then transitive axioms. -/

open ShiQIP

#check (halve_spec : ∀ {d : Desc} {n : ℕ}, d.Valid → 1 ≤ n → n % 2 = 0 → d.HasSchedule (2 * n + 1) →
  (halveDesc d n).Valid ∧ (halveDesc d n).HasSchedule (n + 1) ∧
    value (halveDesc d n) ≤ (1 + Real.sqrt (value d)) / 2 ∧ (value d = 1 → value (halveDesc d n) = 1))
#check (halve_pow : ∀ {d : Desc} {r : ℕ}, 1 ≤ r → d.Valid → d.HasSchedule (2 ^ (r + 1) + 1) →
  (halveDesc d (2 ^ r)).Valid ∧ (halveDesc d (2 ^ r)).HasSchedule (2 ^ r + 1) ∧
    value (halveDesc d (2 ^ r)) ≤ (1 + Real.sqrt (value d)) / 2 ∧
    (value d = 1 → value (halveDesc d (2 ^ r)) = 1))
#check (halve_five_to_three : ∀ {d : Desc}, d.Valid → d.HasSchedule 5 →
  (halveDesc d 2).Valid ∧ (halveDesc d 2).HasSchedule 3 ∧
    value (halveDesc d 2) ≤ (1 + Real.sqrt (value d)) / 2 ∧ (value d = 1 → value (halveDesc d 2) = 1))

#print axioms ShiQIP.runLayer_comp_fam
#print axioms ShiQIP.liftV
#print axioms ShiQIP.hon
#print axioms ShiQIP.hon_liftV
#print axioms ShiQIP.bOp_liftV
#print axioms ShiQIP.bOpH_liftV
#print axioms ShiQIP.σSw_fst_of
#print axioms ShiQIP.σSw_mem
#print axioms ShiQIP.σSw_snd_of
#print axioms ShiQIP.bOp_σSw
#print axioms ShiQIP.slotIn
#print axioms ShiQIP.inReg_halve_iff
#print axioms ShiQIP.inReg_of_slotIn
#print axioms ShiQIP.RestS
#print axioms ShiQIP.eS
#print axioms ShiQIP.eSD
#print axioms ShiQIP.embU
#print axioms ShiQIP.embU_mem
#print axioms ShiQIP.embU_apply
#print axioms ShiQIP.ctl
#print axioms ShiQIP.ctl_mem
#print axioms ShiQIP.proverOp_ctl_apply
#print axioms ShiQIP.sum_embU
#print axioms ShiQIP.transport
#print axioms ShiQIP.swL
#print axioms ShiQIP.proverOp_ctl
#print axioms ShiQIP.hon_sw
#print axioms ShiQIP.comp_sw_of_zero
#print axioms ShiQIP.dRun
#print axioms ShiQIP.pureRun_dilateU_dRun
#print axioms ShiQIP.kron_vanish
#print axioms ShiQIP.support_instrInv
#print axioms ShiQIP.kronH_vanish
#print axioms ShiQIP.tv_vanish
#print axioms ShiQIP.held_toV_le
#print axioms ShiQIP.dRun_future
#print axioms ShiQIP.disp
#print axioms ShiQIP.DispW
#print axioms ShiQIP.DispS
#print axioms ShiQIP.disp_mem
#print axioms ShiQIP.disp_fst
#print axioms ShiQIP.disp_snd
#print axioms ShiQIP.bOp_disp
#print axioms ShiQIP.hon_disp
#print axioms ShiQIP.sum_disp
#print axioms ShiQIP.cpy
#print axioms ShiQIP.cpy_involutive
#print axioms ShiQIP.cpyPerm
#print axioms ShiQIP.cpyL
#print axioms ShiQIP.PA_mul
#print axioms ShiQIP.proverOp_mul
#print axioms ShiQIP.proverOp_cpy
#print axioms ShiQIP.toP_iff_odd
#print axioms ShiQIP.copyW_lt_hPay
#print axioms ShiQIP.cpyL_fix
#print axioms ShiQIP.comp_cpyL
#print axioms ShiQIP.honA
#print axioms ShiQIP.dispF
#print axioms ShiQIP.liftV_vanish
#print axioms ShiQIP.copy_not_dispS
#print axioms ShiQIP.region_not_inReg
#print axioms ShiQIP.dI_avoid_dead
#print axioms ShiQIP.dI_avoid_future
#print axioms ShiQIP.slot_lt
#print axioms ShiQIP.gF_honest
#print axioms ShiQIP.layer_σSw
#print axioms ShiQIP.blockOpH_eq
#print axioms ShiQIP.bOpH_σSw
#print axioms ShiQIP.bOpH_disp
#print axioms ShiQIP.kron_blockMat_mem
#print axioms ShiQIP.dRun_undo
#print axioms ShiQIP.tv_mul_apply
#print axioms ShiQIP.tv_one'
#print axioms ShiQIP.tv_inv
#print axioms ShiQIP.copyW_inReg_iff
#print axioms ShiQIP.cpyL_of_ne
#print axioms ShiQIP.liftV_flip_cpy
#print axioms ShiQIP.swL_cpyL
#print axioms ShiQIP.dispB
#print axioms ShiQIP.gB_honest
#print axioms ShiQIP.sum_liftV
#print axioms ShiQIP.sum_disp_wires
#print axioms ShiQIP.kron_tv
#print axioms ShiQIP.nsq_tv
#print axioms ShiQIP.sum_ite_eq_mul
#print axioms ShiQIP.out_not_region
#print axioms ShiQIP.outBit_congr
#print axioms ShiQIP.fwdP_honest
#print axioms ShiQIP.zero0_congr
#print axioms ShiQIP.bwdP_honest
#print axioms ShiQIP.clean_after_turn
#print axioms ShiQIP.colOf
#print axioms ShiQIP.colOf_iso
#print axioms ShiQIP.exists_unitary_send
#print axioms ShiQIP.value_halve_eq_one_of
#print axioms ShiQIP.value_halve_eq_one
#print axioms ShiQIP.okBool_of_wires
#print axioms ShiQIP.wires_of_okBool
#print axioms ShiQIP.cnot_ne_of_okBool
#print axioms ShiQIP.okBool_mono
#print axioms ShiQIP.okBool_swapGates
#print axioms ShiQIP.okBool_swapRange
#print axioms ShiQIP.okBool_ctrlGates
#print axioms ShiQIP.okBool_ztGates
#print axioms ShiQIP.held_halve_priv
#print axioms ShiQIP.held_halve_msg
#print axioms ShiQIP.GoodAt
#print axioms ShiQIP.GoodAt.append
#print axioms ShiQIP.goodAt_nil
#print axioms ShiQIP.goodAt_ite
#print axioms ShiQIP.goodAt_dBlock
#print axioms ShiQIP.inv_wires_okBool
#print axioms ShiQIP.goodAt_adj
#print axioms ShiQIP.goodAt_swapMsg
#print axioms ShiQIP.okBool_onF
#print axioms ShiQIP.okBool_onB
#print axioms ShiQIP.hasSchedule_halveDesc
#print axioms ShiQIP.nodup_zt_nat
#print axioms ShiQIP.halveDesc_valid
#print axioms ShiQIP.halve_spec
#print axioms ShiQIP.halve_pow
#print axioms ShiQIP.halve_five_to_three
