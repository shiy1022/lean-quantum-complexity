import QIP.ParallelRepeat

/-! Fresh-import audit for Q25: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix ShiShallow

#check (value_pairDesc : ∀ {d₁ d₂ : Desc}, d₁.numMsgs = d₂.numMsgs → d₁.Valid → d₂.Valid →
  value (pairDesc d₁ d₂) = value d₁ * value d₂)
#check (pairDesc_valid : ∀ {d₁ d₂ : Desc}, d₁.numMsgs = d₂.numMsgs →
  d₁.msgs.map Message.dir = d₂.msgs.map Message.dir → d₁.Valid → d₂.Valid →
    (pairDesc d₁ d₂).Valid)
#check (value_parRepeat : ∀ {d : Desc}, d.Valid → ∀ {k : ℕ}, 1 ≤ k →
  value (parRepeat d k) = value d ^ k)
#check (parRepeat_valid : ∀ {d : Desc}, d.Valid → ∀ k, (parRepeat d k).Valid)
#check (hasSchedule_parRepeat : ∀ {d : Desc} {m : ℕ}, d.HasSchedule m → ∀ k,
  (parRepeat d k).HasSchedule m)
#check (totalWires_parRepeat : ∀ (d : Desc) {k : ℕ}, 1 ≤ k →
  (parRepeat d k).totalWires = k * d.totalWires + (k - 1))
#check (gateCount_parRepeat : ∀ {d : Desc}, d.Valid → ∀ {k : ℕ}, 1 ≤ k →
  (parRepeat d k).gateCount = k * d.gateCount + 33 * (k - 1))
#check (communication_parRepeat : ∀ (d : Desc) {k : ℕ}, 1 ≤ k →
  (parRepeat d k).communication = k * d.communication)

#print axioms ShiQIP.psum
#print axioms ShiQIP.zw
#print axioms ShiQIP.psum_add_getD_le
#print axioms ShiQIP.exists_segment
#print axioms ShiQIP.segment_unique
#print axioms ShiQIP.psum_zw
#print axioms ShiQIP.getD_zw
#print axioms ShiQIP.sum_zw
#print axioms ShiQIP.segIdx
#print axioms ShiQIP.segIdx_spec
#print axioms ShiQIP.segIdx_eq
#print axioms ShiQIP.pairMsgs
#print axioms ShiQIP.pairMsgs_widths
#print axioms ShiQIP.pairMsgs_dirs
#print axioms ShiQIP.length_pairMsgs
#print axioms ShiQIP.segs
#print axioms ShiQIP.segs_sum
#print axioms ShiQIP.segs_length
#print axioms ShiQIP.msgWidth_eq
#print axioms ShiQIP.msgOffset_eq
#print axioms ShiQIP.inReg_iff_segIdx
#print axioms ShiQIP.pos₁
#print axioms ShiQIP.pos₂
#print axioms ShiQIP.pairBlock
#print axioms ShiQIP.pairDesc
#print axioms ShiQIP.segs_pairDesc
#print axioms ShiQIP.totalWires_pairDesc
#print axioms ShiQIP.numMsgs_pairDesc
#print axioms ShiQIP.segs_length_eq
#print axioms ShiQIP.pos₁_of_seg
#print axioms ShiQIP.pos₂_of_seg
#print axioms ShiQIP.pos₁_lt
#print axioms ShiQIP.pos₂_lt
#print axioms ShiQIP.segIdx_pos₁
#print axioms ShiQIP.segIdx_pos₂
#print axioms ShiQIP.pos₁_pos
#print axioms ShiQIP.pos₂_pos
#print axioms ShiQIP.pos₁_inj
#print axioms ShiQIP.pos₂_inj
#print axioms ShiQIP.pos₁_ne_pos₂
#print axioms ShiQIP.segIdx_shift
#print axioms ShiQIP.segIdx_pairDesc
#print axioms ShiQIP.inReg_pair_iff
#print axioms ShiQIP.not_inReg_pair_zero
#print axioms ShiQIP.emb₁
#print axioms ShiQIP.emb₂
#print axioms ShiQIP.inReg_emb₁
#print axioms ShiQIP.inReg_emb₂
#print axioms ShiQIP.embSum
#print axioms ShiQIP.totalWires_pair_eq
#print axioms ShiQIP.ancWire
#print axioms ShiQIP.ancWire_notMem
#print axioms ShiQIP.eq_ancWire_of_notMem
#print axioms ShiQIP.outsideUnique
#print axioms ShiQIP.pairSigma
#print axioms ShiQIP.pairSigma_apply
#print axioms ShiQIP.ancWire_not_inReg
#print axioms ShiQIP.mem_range_of_inReg
#print axioms ShiQIP.regMap
#print axioms ShiQIP.regMap_bijective
#print axioms ShiQIP.pairTau
#print axioms ShiQIP.pairTau_apply
#print axioms ShiQIP.wireSplitE_snd
#print axioms ShiQIP.wireSplitE_symm_apply
#print axioms ShiQIP.wireSplitE_fst_apply
#print axioms ShiQIP.pair_reg_read
#print axioms ShiQIP.pair_reg_write
#print axioms ShiQIP.pairSigma_zero
#print axioms ShiQIP.pair_zero
#print axioms ShiQIP.mem_range_emb
#print axioms ShiQIP.emb₁_ne_emb₂
#print axioms ShiQIP.emb₁_ne_anc
#print axioms ShiQIP.emb₂_ne_anc
#print axioms ShiQIP.kron_embSplit₁
#print axioms ShiQIP.kron_embSplit₂
#print axioms ShiQIP.blockTens_mul_blockTens
#print axioms ShiQIP.layerMat_relabel₁
#print axioms ShiQIP.layerMat_relabel₂
#print axioms ShiQIP.blocks_pairDesc_getD
#print axioms ShiQIP.pair_block_prod
#print axioms ShiQIP.layerMat_toffoli_apply
#print axioms ShiQIP.toffoliFun_involutive
#print axioms ShiQIP.toffoli_conj_basisEffect
#print axioms ShiQIP.outW₁
#print axioms ShiQIP.outW₂
#print axioms ShiQIP.pairF
#print axioms ShiQIP.pair_block_last
#print axioms ShiQIP.pair_final_effect
#print axioms ShiQIP.pairData
#print axioms ShiQIP.value_pairDesc
#print axioms ShiQIP.dirOk
#print axioms ShiQIP.msgHeld_iff
#print axioms ShiQIP.held_iff
#print axioms ShiQIP.pos₁_priv
#print axioms ShiQIP.pos₂_priv
#print axioms ShiQIP.dirs_pairDesc
#print axioms ShiQIP.held_pos₁
#print axioms ShiQIP.held_pos₂
#print axioms ShiQIP.held_relabel₁
#print axioms ShiQIP.held_relabel₂
#print axioms ShiQIP.okBool_relabel₁
#print axioms ShiQIP.okBool_relabel₂
#print axioms ShiQIP.okBool_toffoliGates
#print axioms ShiQIP.blocksOkFrom_of
#print axioms ShiQIP.alternates_congr
#print axioms ShiQIP.pairDesc_valid
#print axioms ShiQIP.repeatAux
#print axioms ShiQIP.parRepeat
#print axioms ShiQIP.numMsgs_repeatAux
#print axioms ShiQIP.dirs_repeatAux
#print axioms ShiQIP.repeatAux_valid
#print axioms ShiQIP.value_repeatAux
#print axioms ShiQIP.parRepeat_valid
#print axioms ShiQIP.numMsgs_parRepeat
#print axioms ShiQIP.schedule_parRepeat
#print axioms ShiQIP.hasSchedule_parRepeat
#print axioms ShiQIP.value_parRepeat
#print axioms ShiQIP.totalWires_repeatAux
#print axioms ShiQIP.totalWires_parRepeat
#print axioms ShiQIP.communication_pairDesc
#print axioms ShiQIP.communication_repeatAux
#print axioms ShiQIP.communication_parRepeat
#print axioms ShiQIP.sum_range_getD_length
#print axioms ShiQIP.gateCount_pairDesc
#print axioms ShiQIP.gateCount_repeatAux
#print axioms ShiQIP.gateCount_parRepeat
