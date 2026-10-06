import QIP.TesterProduct
import QIP.Circuit.Relabel

/-! Fresh-import audit for the Q25 groundwork: exact statement types, then axioms. -/

open ShiQIP ShiQuantum Matrix ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

#check (PairData.value_eq : ∀ {d₁ d₂ d : Desc}, PairData d₁ d₂ d → d₁.numMsgs = d.numMsgs →
  d₂.numMsgs = d.numMsgs → value d = value d₁ * value d₂)
#check (layerMat_map : ∀ {N M : ℕ} (f : Fin N ↪ Fin M) (l : List (Instr N)),
  layerMat (l.map (instrMap f)) =
    (layerMat l ⊗ₖ (1 : Matrix (Outside f → Bool) (Outside f → Bool) ℂ)).submatrix
      (embSplit f) (embSplit f))

#print axioms ShiQIP.traceRight_submatrix_prodMap
#print axioms ShiQIP.kron_one_submatrix
#print axioms ShiQIP.histMap
#print axioms ShiQIP.relabel
#print axioms ShiQIP.isStrategy_relabel
#print axioms ShiQIP.relabel_relabel_symm
#print axioms ShiQIP.sdpVal_relabel
#print axioms ShiQIP.tens
#print axioms ShiQIP.histStep
#print axioms ShiQIP.histStep_apply
#print axioms ShiQIP.transfer_tens
#print axioms ShiQIP.blockTens
#print axioms ShiQIP.mul_tens
#print axioms ShiQIP.sum_split
#print axioms ShiQIP.ancZero
#print axioms ShiQIP.tens_conj
#print axioms ShiQIP.tens_congr
#print axioms ShiQIP.testerAt
#print axioms ShiQIP.testerAt_posSemidef
#print axioms ShiQIP.value_eq_sdpVal_testerAt
#print axioms ShiQIP.PairData
#print axioms ShiQIP.PairData.hE
#print axioms ShiQIP.PairData.hE_succ
#print axioms ShiQIP.PairData.zeroCol
#print axioms ShiQIP.PairData.transMat_zero
#print axioms ShiQIP.PairData.zeroCol_tens
#print axioms ShiQIP.PairData.transMat_eq
#print axioms ShiQIP.PairData.transMat_last
#print axioms ShiQIP.PairData.tester_eq
#print axioms ShiQIP.PairData.value_eq
#print axioms ShiQIP.Outside
#print axioms ShiQIP.embSplit
#print axioms ShiQIP.embSplit_fst
#print axioms ShiQIP.embSplit_snd
#print axioms ShiQIP.embSplit_update
#print axioms ShiQIP.embSplit_symm_update
#print axioms ShiQIP.instrMap
#print axioms ShiQIP.sliceAt
#print axioms ShiQIP.apply1_map
#print axioms ShiQIP.instrMap_apply
#print axioms ShiQIP.sliceAt_apply
#print axioms ShiQIP.runLayer_map
#print axioms ShiQIP.runLayer_map_apply
#print axioms ShiQIP.layerMat_map
#print axioms ShiQIP.Gate.relabel
#print axioms ShiQIP.Gate.wires_relabel
#print axioms ShiQIP.toInstr?_relabel
#print axioms ShiQIP.filterMap_relabel
