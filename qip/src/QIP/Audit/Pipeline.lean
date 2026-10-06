import QIP.Pipeline

/-! Fresh-import audit for schedule normalization and the semantic pipeline to three messages:
statement types, then transitive axioms. -/

open ShiQIP

#check (value_appendV : ∀ {d : Desc}, d.Valid → value (appendV d) = value d)
#check (threeDesc_spec : ∀ {d : Desc}, d.Valid →
  (threeDesc d).Valid ∧ (threeDesc d).HasSchedule 3 ∧
    (2 / 3 ≤ value d → value (threeDesc d) = 1) ∧ (value d ≤ 1 / 3 → value (threeDesc d) ≤ 1 / 3))
#check (hsize_threeDesc_le : ∀ {d : Desc}, d.Valid →
  hsize (threeDesc d) ≤ 38 * 72 * 189 ^ 2 * 94 ^ 11 * 465 * (hsize d + 1) ^ 14)

#print axioms ShiQIP.appendV
#print axioms ShiQIP.numMsgs_appendV
#print axioms ShiQIP.totalWires_appendV
#print axioms ShiQIP.alternates_cons_cons
#print axioms ShiQIP.alternates_iff_dirs
#print axioms ShiQIP.msgHeld_append_zero
#print axioms ShiQIP.held_appendV
#print axioms ShiQIP.eWA
#print axioms ShiQIP.eQA
#print axioms ShiQIP.eWA_val
#print axioms ShiQIP.msgOffset_appendV
#print axioms ShiQIP.msgWidth_appendV
#print axioms ShiQIP.msgWidth_appendV_last
#print axioms ShiQIP.inReg_appendV
#print axioms ShiQIP.not_inReg_appendV_last
#print axioms ShiQIP.τA
#print axioms ShiQIP.blocks_appendV_getD
#print axioms ShiQIP.blocks_appendV_last
#print axioms ShiQIP.blockMat_appendV
#print axioms ShiQIP.blockMat_appendV_last
#print axioms ShiQIP.restT
#print axioms ShiQIP.eQA_apply
#print axioms ShiQIP.split_τA
#print axioms ShiQIP.regSet_τA
#print axioms ShiQIP.turnVec_rest
#print axioms ShiQIP.zeroVec_eQA
#print axioms ShiQIP.kron_submatrix_mulVecA
#print axioms ShiQIP.pureRun_rest
#print axioms ShiQIP.sum_norm_iso
#print axioms ShiQIP.zRegA
#print axioms ShiQIP.regA_eq_zero
#print axioms ShiQIP.lastW
#print axioms ShiQIP.lastW_iso
#print axioms ShiQIP.turnVec_last
#print axioms ShiQIP.outBit_eQA
#print axioms ShiQIP.accept_restT
#print axioms ShiQIP.extV
#print axioms ShiQIP.extV_iso
#print axioms ShiQIP.extT
#print axioms ShiQIP.accept_extT
#print axioms ShiQIP.value_appendV
#print axioms ShiQIP.dir_getD_cases
#print axioms ShiQIP.dirs_eq_std
#print axioms ShiQIP.hasSchedule_of_last
#print axioms ShiQIP.appendV_valid
#print axioms ShiQIP.hasSchedule_appendV
#print axioms ShiQIP.normDesc
#print axioms ShiQIP.normDesc_spec
#print axioms ShiQIP.pipeExp
#print axioms ShiQIP.compDesc
#print axioms ShiQIP.threeDesc
#print axioms ShiQIP.compDesc_spec
#print axioms ShiQIP.threeDesc_spec
#print axioms ShiQIP.sum_range_list_map
#print axioms ShiQIP.gateCount_padDesc
#print axioms ShiQIP.gateCount_appendV
#print axioms ShiQIP.gateCount_flagDesc
#print axioms ShiQIP.length_swapAll_le
#print axioms ShiQIP.gateCount_bellDesc_le
#print axioms ShiQIP.totalWires_rejectDesc
#print axioms ShiQIP.gateCount_rejectDesc
#print axioms ShiQIP.hsize_normDesc
#print axioms ShiQIP.hsize_perfDesc
#print axioms ShiQIP.hsize_padTo
#print axioms ShiQIP.hsize_parRepeat
#print axioms ShiQIP.hsize_threeDesc_le
