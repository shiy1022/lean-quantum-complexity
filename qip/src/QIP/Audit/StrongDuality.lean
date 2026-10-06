import QIP.SDP.StrongDuality

/-! Fresh-import audit for Q23: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix
open scoped ComplexOrder MatrixOrder Kronecker

#check (exists_dualCert_value : ∀ (d : Desc) {η : ℝ}, 0 < η →
  ∃ t, value d ≤ t ∧ t ≤ value d + η ∧ Nonempty (DualCert d.numMsgs (tester d) t))
#check (value_eq_sInf_cert : ∀ d : Desc,
  value d = sInf {t | Nonempty (DualCert d.numMsgs (tester d) t)})
#check (exists_dualCert_le : ∀ {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] [∀ i, Nonempty (X i)]
  [∀ i, Nonempty (Y i)] {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ}, T.IsHermitian →
  ∀ {V : ℝ}, (∀ Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ, IsStrategy r Q →
    (trace (T * Q r)).re ≤ V) → ∀ {η : ℝ}, 0 < η → ∃ t, t ≤ V + η ∧ Nonempty (DualCert r T t))

#print axioms ShiQuantum.conic_approx_duality
#print axioms ShiQIP.matrix_locallyConvexSpace
#print axioms ShiQIP.single_eq_re_smul_add
#print axioms ShiQIP.exists_trace_rep
#print axioms ShiQIP.exists_herm_rep
#print axioms ShiQIP.posSemidef_of_trace_nonneg
#print axioms ShiQIP.le_of_trace_le
#print axioms ShiQIP.telescope
#print axioms ShiQIP.cardProd
#print axioms ShiQIP.cardProd_succ
#print axioms ShiQIP.cardProd_pos
#print axioms ShiQIP.psdCone
#print axioms ShiQIP.psdCone_smul
#print axioms ShiQIP.convex_psdCone
#print axioms ShiQIP.isClosed_psdCone
#print axioms ShiQIP.zeroView
#print axioms ShiQIP.lastView
#print axioms ShiQIP.constrMap
#print axioms ShiQIP.constrMap_apply
#print axioms ShiQIP.continuous_constrMap
#print axioms ShiQIP.objMap
#print axioms ShiQIP.objMap_apply
#print axioms ShiQIP.lastView_single_last
#print axioms ShiQIP.lastView_single_ne
#print axioms ShiQIP.continuous_objMap
#print axioms ShiQIP.gauge
#print axioms ShiQIP.gauge_apply
#print axioms ShiQIP.gauge_nonneg
#print axioms ShiQIP.continuous_gauge
#print axioms ShiQIP.isCompact_gauge_le
#print axioms ShiQIP.posDir
#print axioms ShiQIP.trace_causalRes
#print axioms ShiQIP.posDir_constrMap
#print axioms ShiQIP.mixedStrategy
#print axioms ShiQIP.mixedStrategy_posDef
#print axioms ShiQIP.mixedStrategy_isStrategy
#print axioms ShiQIP.slotFun
#print axioms ShiQIP.zeroFun
#print axioms ShiQIP.constrSpace_decomp
#print axioms ShiQIP.multW
#print axioms ShiQIP.multZero
#print axioms ShiQIP.multW_spec
#print axioms ShiQIP.multZero_spec
#print axioms ShiQIP.certW
#print axioms ShiQIP.certZ
#print axioms ShiQIP.certW_of_lt
#print axioms ShiQIP.certW_self
#print axioms ShiQIP.certW_isHermitian
#print axioms ShiQIP.certZ_isHermitian
#print axioms ShiQIP.traceRight_certW_isHermitian
#print axioms ShiQIP.traceRight_zero'
#print axioms ShiQIP.dual_slot_form
#print axioms ShiQIP.single_mem_psdCone
#print axioms ShiQIP.dual_single
#print axioms ShiQIP.exists_dualCert_le
#print axioms ShiQIP.reg_nonempty
#print axioms ShiQIP.pairing_le_value
#print axioms ShiQIP.exists_dualCert_value
#print axioms ShiQIP.value_eq_sInf_cert
