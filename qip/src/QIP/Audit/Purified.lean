import QIP.Purified

/-! Fresh-import audit for Q17 (purified strategies): statement types, then axioms. -/

open ShiQIP ShiQuantum Matrix

#check (exists_isoProver : ∀ {d : Desc} (P : Prover d),
  ∃ T : IsoStrategy (Reg d) (Reg d) d.numMsgs, accept T.toOp = accept P)
#check (exists_iso_of_op : ∀ {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] {r : ℕ} (S : OpStrategy X Y r),
  ∃ T : IsoStrategy X Y r, ∀ k ≤ r, stratOp T.toOp k = stratOp S k)

#print axioms ShiQIP.IsoStrategy
#print axioms ShiQIP.IsoStrategy.toOp
#print axioms ShiQIP.envT
#print axioms ShiQIP.envT_fintype
#print axioms ShiQIP.envT_decEq
#print axioms ShiQIP.stin
#print axioms ShiQIP.stin_spec
#print axioms ShiQIP.envStep
#print axioms ShiQIP.dilOut
#print axioms ShiQIP.dilV
#print axioms ShiQIP.dilV_iso
#print axioms ShiQIP.dilate
#print axioms ShiQIP.redE
#print axioms ShiQIP.regroupOut
#print axioms ShiQIP.dilOf
#print axioms ShiQIP.redE_linkStep
#print axioms ShiQIP.redE_memState
#print axioms ShiQIP.stratOp_dilate
#print axioms ShiQIP.exists_iso_of_op
#print axioms ShiQIP.exists_isoProver
