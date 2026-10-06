import QIP.SDP.Product

/-! Fresh-import audit for Q24: exact statement types, then transitive axioms. -/

open ShiQIP ShiQuantum Matrix
open scoped ComplexOrder MatrixOrder Kronecker

#check (sdpVal_prod : ∀ {X₁ Y₁ X₂ Y₂ : ℕ → Type} [∀ i, Fintype (X₁ i)] [∀ i, Fintype (Y₁ i)]
  [∀ i, Fintype (X₂ i)] [∀ i, Fintype (Y₂ i)] [∀ i, DecidableEq (X₁ i)]
  [∀ i, DecidableEq (Y₁ i)] [∀ i, DecidableEq (X₂ i)] [∀ i, DecidableEq (Y₂ i)]
  [∀ i, Nonempty (X₁ i)] [∀ i, Nonempty (Y₁ i)] [∀ i, Nonempty (X₂ i)] [∀ i, Nonempty (Y₂ i)]
  {r : ℕ} {T₁ : Matrix (Hist X₁ Y₁ r) (Hist X₁ Y₁ r) ℂ}
  {T₂ : Matrix (Hist X₂ Y₂ r) (Hist X₂ Y₂ r) ℂ}, T₁.PosSemidef → T₂.PosSemidef →
  sdpVal (prodMat T₁ T₂) = sdpVal T₁ * sdpVal T₂)
#check (value_eq_sdpVal : ∀ d : Desc, value d = sdpVal (tester d))

#print axioms ShiQIP.kron_le_kron
#print axioms ShiQIP.submatrix_le_submatrix
#print axioms ShiQIP.trace_submatrix_equiv
#print axioms ShiQIP.psd_of_kron_one
#print axioms ShiQIP.posSemidef_of_ge
#print axioms ShiQIP.DualCert.posSemidef_Z
#print axioms ShiQIP.DualCert.Z_posSemidef
#print axioms ShiQIP.DualCert.W_posSemidef
#print axioms ShiQIP.sdpVal
#print axioms ShiQIP.sdpVal_nonempty
#print axioms ShiQIP.sdpVal_bddAbove
#print axioms ShiQIP.pairing_le_sdpVal
#print axioms ShiQIP.sdpVal_le_of_cert
#print axioms ShiQIP.sdpVal_nonneg
#print axioms ShiQIP.histEquiv
#print axioms ShiQIP.midEquiv
#print axioms ShiQIP.midEquiv_apply
#print axioms ShiQIP.histEquiv_succ_apply
#print axioms ShiQIP.prodMat
#print axioms ShiQIP.prodMid
#print axioms ShiQIP.prodMat_mul
#print axioms ShiQIP.trace_prodMat
#print axioms ShiQIP.prodMat_posSemidef
#print axioms ShiQIP.prodMat_le
#print axioms ShiQIP.traceRight_prodMat_succ
#print axioms ShiQIP.prodMat_kron_one
#print axioms ShiQIP.prodMid_kron_one
#print axioms ShiQIP.traceRight_prodMid
#print axioms ShiQIP.prodMid_le
#print axioms ShiQIP.prodMat_zero_smul_one
#print axioms ShiQIP.isStrategy_prod
#print axioms ShiQIP.trace_prodMat_mul
#print axioms ShiQIP.DualCert.prod
#print axioms ShiQIP.re_mul_of_nonneg
#print axioms ShiQIP.sdpVal_prod
#print axioms ShiQIP.value_eq_sdpVal
