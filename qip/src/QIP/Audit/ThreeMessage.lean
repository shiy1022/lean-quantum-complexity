import QIP.ThreeMessage

/-! Fresh-import audit for Q39-Q40 (the transformed verifier family and `QIP = QIP(3)`):
statement types, then transitive axioms. -/

open ShiQIP

#check (qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3)
#check (@VerifierFamily.three_decides : ∀ {F : VerifierFamily} {A : PromiseProblem}, Decides F A →
  Decides F.three A)
#check (VerifierFamily.three_schedule : ∀ (F : VerifierFamily) (x : Str), (F.three.desc x).HasSchedule 3)

#print axioms ShiQIP.threeC
#print axioms ShiQIP.threeBound
#print axioms ShiQIP.hsize_three_le
#print axioms ShiQIP.VerifierFamily.three
#print axioms ShiQIP.VerifierFamily.three_schedule
#print axioms ShiQIP.VerifierFamily.three_decides
#print axioms ShiQIP.qip_subset_qip3
#print axioms ShiQIP.qip_eq_qip3
