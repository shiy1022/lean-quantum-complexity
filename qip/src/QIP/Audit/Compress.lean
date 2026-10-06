import QIP.Compress

/-! Fresh-import audit for Q32 iterated compression: statement types, then transitive axioms. -/

open ShiQIP ShiQIP.Arith

#check (compressR_spec : ∀ (r : ℕ) (d : Desc), d.Valid → d.HasSchedule (padM r) →
  (compressR r d).Valid ∧ (compressR r d).HasSchedule 3 ∧ (value d = 1 → value (compressR r d) = 1) ∧
    ∀ ε : ℝ, ε ≤ 1 → value d ≤ 1 - ε → value (compressR r d) ≤ 1 - ε / 4 ^ r)
#check (compressR_sound : ∀ {r : ℕ} {d : Desc}, d.Valid → d.HasSchedule (padM r) → ∀ {ε : ℝ},
  0 ≤ ε → ε ≤ 1 → value d ≤ 1 - ε → value (compressR r d) ≤ 1 - ε / (padM r : ℝ) ^ 2)
#check (hsize_compressR_le : ∀ (r : ℕ) (d : Desc), d.HasSchedule (padM r) →
  hsize (compressR r d) ≤ 2010 ^ r * hsize d)

#print axioms ShiQIP.compressR
#print axioms ShiQIP.compressR_zero
#print axioms ShiQIP.compressR_succ
#print axioms ShiQIP.compressR_spec
#print axioms ShiQIP.compressR_sound
#print axioms ShiQIP.sum_wd_le
#print axioms ShiQIP.communication_le
#print axioms ShiQIP.held0_length_le
#print axioms ShiQIP.sum_hw_le
#print axioms ShiQIP.totalWires_halveDesc_le
#print axioms ShiQIP.length_swapRange
#print axioms ShiQIP.length_swapMsg
#print axioms ShiQIP.length_onF_le
#print axioms ShiQIP.length_onB_le
#print axioms ShiQIP.length_ztGates
#print axioms ShiQIP.bl
#print axioms ShiQIP.sum_bl_le
#print axioms ShiQIP.bl_le
#print axioms ShiQIP.wd_le
#print axioms ShiQIP.length_adjB
#print axioms ShiQIP.sum_comp_le
#print axioms ShiQIP.length_ite_le
#print axioms ShiQIP.hBlock_one_le
#print axioms ShiQIP.hBlock_mid_le
#print axioms ShiQIP.hBlock_last_le
#print axioms ShiQIP.gateCount_halveDesc_le
#print axioms ShiQIP.hsize
#print axioms ShiQIP.hsize_halveDesc_le
#print axioms ShiQIP.hsize_compressR_le
