import QIP.Bell.Prefix
import Quantum.BellBound

/-! Fresh-import audit for the Q27 groundwork: statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix

#check (PrefixData.pureRun_prefix : ∀ {d D : Desc} (Pf : PrefixData d D)
  (T : IsoStrategy (Reg D) (Reg D) D.numMsgs), ∀ j < d.numMsgs,
    pureRun T j = Pf.embV (pureRun (Pf.restrict T) j))
#check (accept_pureRun : ∀ {d : Desc} (T : IsoStrategy (Reg d) (Reg d) d.numMsgs),
  accept T.toOp = (star (pureRun T d.numMsgs) ⬝ᵥ
    (acceptEffect d (T.M d.numMsgs) *ᵥ pureRun T d.numMsgs)).re)
#check (half_add_sqrt_le : ∀ {p : ℝ}, 0 ≤ p → p ≤ 1 →
  1 / 2 + Real.sqrt (p * (1 - p)) ≤ 1 - (1 / 2 - p) ^ 2)

#print axioms ShiQuantum.fidelity_pureState_sq
#print axioms ShiQuantum.fidelity_diag_half_sq
#print axioms ShiQuantum.half_add_sqrt_le
#print axioms ShiQuantum.bell_bound_third
#print axioms ShiQuantum.sqrtTwo_inv_mul_self
#print axioms ShiQuantum.bellVecB
#print axioms ShiQuantum.bellVecB_norm
#print axioms ShiQuantum.traceRight_bellVecB
#print axioms ShiQuantum.assocVec
#print axioms ShiQuantum.traceRight_one_kron_mul_comm
#print axioms ShiQuantum.traceRight_conj_isometry
#print axioms ShiQuantum.pureState_mulVec
#print axioms ShiQuantum.traceRight_traceRight_assoc
#print axioms ShiQuantum.bell_prob_le
#print axioms ShiQuantum.embFalse
#print axioms ShiQuantum.embFalse_isometry
#print axioms ShiQuantum.bell_prob_eq_one
#print axioms ShiQIP.submatrix_pureState
#print axioms ShiQIP.kronecker_pureState
#print axioms ShiQIP.turnVec
#print axioms ShiQIP.proverStep_pureState
#print axioms ShiQIP.pureRun
#print axioms ShiQIP.stateAfterBlock_pureRun
#print axioms ShiQIP.accept_pureRun
#print axioms ShiQIP.bellShift
#print axioms ShiQIP.bellB
#print axioms ShiQIP.bellOut
#print axioms ShiQIP.bellMsgOff
#print axioms ShiQIP.bellO
#print axioms ShiQIP.swapAll
#print axioms ShiQIP.bellFinal
#print axioms ShiQIP.bellBlock
#print axioms ShiQIP.bellDesc
#print axioms ShiQIP.numMsgs_bellDesc
#print axioms ShiQIP.totalWires_bellDesc
#print axioms ShiQIP.schedule_bellDesc
#print axioms ShiQIP.bellShift_lt
#print axioms ShiQIP.bellShift_inj
#print axioms ShiQIP.bellEmb
#print axioms ShiQIP.segs_bellDesc
#print axioms ShiQIP.psum_bell
#print axioms ShiQIP.getD_bell
#print axioms ShiQIP.inReg_bellEmb
#print axioms ShiQIP.mem_range_bellEmb
#print axioms ShiQIP.blocks_bell_getD
#print axioms ShiQIP.blockMat_bell_lt
#print axioms ShiQIP.bellG
#print axioms ShiQIP.blockMat_bell_last
#print axioms ShiQIP.bellPrefix
#print axioms ShiQIP.PrefixData
#print axioms ShiQIP.PrefixData.regMapP
#print axioms ShiQIP.PrefixData.regMapP_bijective
#print axioms ShiQIP.PrefixData.τ
#print axioms ShiQIP.PrefixData.τ_apply
#print axioms ShiQIP.PrefixData.embV
#print axioms ShiQIP.PrefixData.restrict
#print axioms ShiQIP.PrefixData.restrict_V
#print axioms ShiQIP.PrefixData.regSet
#print axioms ShiQIP.PrefixData.regSet_apply
#print axioms ShiQIP.PrefixData.turnVec_apply
#print axioms ShiQIP.PrefixData.embSplit_regSet_snd
#print axioms ShiQIP.PrefixData.embSplit_regSet_fst
#print axioms ShiQIP.PrefixData.τ_reg
#print axioms ShiQIP.PrefixData.turnVec_embV
#print axioms ShiQIP.PrefixData.mulVec_embV
#print axioms ShiQIP.PrefixData.zero_embV
#print axioms ShiQIP.PrefixData.pureRun_prefix
#print axioms ShiQIP.PrefixData.pureRun_prefix_last
