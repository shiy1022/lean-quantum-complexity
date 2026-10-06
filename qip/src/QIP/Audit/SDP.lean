import QIP.SDP.WeakDuality

/-! Fresh-import audit for Q22: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix
open scoped ComplexOrder MatrixOrder Kronecker

#check (DualCert.accept_le : ∀ {d : Desc} {t : ℝ}, DualCert d.numMsgs (tester d) t →
  ∀ P : Prover d, accept P ≤ t)
#check (DualCert.value_le : ∀ {d : Desc} {t : ℝ}, DualCert d.numMsgs (tester d) t → value d ≤ t)
#check (accept_le_trace_tester : ∀ {d : Desc} (P : Prover d), accept P ≤
  (trace (tester d)).re * ∏ i ∈ Finset.range d.numMsgs, (Fintype.card (Reg d i) : ℝ))
#check (psd_le_trace_smul_one : ∀ {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ},
  M.PosSemidef → M ≤ (((trace M).re : ℝ) : ℂ) • (1 : Matrix n n ℂ))

#print axioms ShiQIP.trace_kron_one_mul
#print axioms ShiQIP.trace_mul_kron_one
#print axioms ShiQIP.trace_causal_link
#print axioms ShiQIP.causalMap
#print axioms ShiQIP.causalMap_isHermitian
#print axioms ShiQIP.isStrategy_iff_causalMap
#print axioms ShiQIP.trace_mul_causalRes
#print axioms ShiQIP.pairing_causalMap
#print axioms ShiQIP.re_trace_mul_mono
#print axioms ShiQIP.DualCert.weak_duality
#print axioms ShiQIP.DualCert.accept_le
#print axioms ShiQIP.DualCert.value_le
#print axioms ShiQIP.quad_le_trace_mul
#print axioms ShiQIP.psd_le_trace_smul_one
#print axioms ShiQIP.scalarWeight_succ
#print axioms ShiQIP.kron_smul_one
#print axioms ShiQIP.traceRight_smul_one
#print axioms ShiQIP.scalarCert
#print axioms ShiQIP.pairing_le_trace_mul_card
#print axioms ShiQIP.accept_le_trace_tester
