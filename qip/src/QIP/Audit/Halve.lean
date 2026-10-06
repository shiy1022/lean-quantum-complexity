import QIP.Halve.Desc

/-! Fresh-import audit for the Q28 zero test and the Q31 halving syntax: statement types, then
transitive axioms. -/

open ShiQIP ShiShallow

#check (runLayer_zt : ∀ {n : ℕ} (S anc : List (Fin n)) (c t : Fin n),
  (c :: t :: (S ++ anc)).Nodup → S.length ≤ anc.length → ∀ (ψ : QState n) (y : Bits n),
    (∀ a ∈ anc, y a = false) →
    runLayer ((ztGates c t (S.map Fin.val) (anc.map Fin.val)).filterMap (Gate.toInstr? n)) ψ y =
      ψ (ztFun c t S y))
#check (numMsgs_halveDesc : ∀ (d : Desc) (n : ℕ), (halveDesc d n).numMsgs = n + 1)

#print axioms ShiQIP.ncaInstrs
#print axioms ShiQIP.runLayer_nca
#print axioms ShiQIP.ztFun
#print axioms ShiQIP.ncaGates
#print axioms ShiQIP.ztGates
#print axioms ShiQIP.filterMap_ncaGates
#print axioms ShiQIP.runLayer_zt
#print axioms ShiQIP.wd
#print axioms ShiQIP.hw
#print axioms ShiQIP.held0
#print axioms ShiQIP.hCoin
#print axioms ShiQIP.hOut
#print axioms ShiQIP.hCa
#print axioms ShiQIP.hAnc
#print axioms ShiQIP.hPriv
#print axioms ShiQIP.hMsgs
#print axioms ShiQIP.hOff
#print axioms ShiQIP.hPay
#print axioms ShiQIP.swapMsg
#print axioms ShiQIP.onF
#print axioms ShiQIP.onB
#print axioms ShiQIP.fwdStep
#print axioms ShiQIP.bwdStep
#print axioms ShiQIP.hBlock
#print axioms ShiQIP.halveDesc
#print axioms ShiQIP.numMsgs_halveDesc
#print axioms ShiQIP.priv_halveDesc
#print axioms ShiQIP.length_hMsgs
#print axioms ShiQIP.width_hMsgs
#print axioms ShiQIP.msgOffset_halveDesc
#print axioms ShiQIP.dir_halveDesc
#print axioms ShiQIP.totalWires_halveDesc
#print axioms ShiQIP.hOff_succ
#print axioms ShiQIP.hOff_mono
#print axioms ShiQIP.hPriv_le_hOff
