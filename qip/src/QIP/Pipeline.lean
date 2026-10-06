import QIP.Compress
import QIP.Normalize
import QIP.PerfectCompleteness
import QIP.ParallelRepeat


/-!
# The semantic pipeline to three messages

`threeDesc d`: normalize the schedule, make completeness perfect (Bell test), pad to
`M = 2 ^ (r + 1) + 1` messages, halve `r` times, and repeat `K = 72 M ^ 2` times in parallel.
For every valid `d` (**`threeDesc_spec`**): the result is valid, has the three-message schedule,
accepts with certainty if `value d ≥ 2/3`, and has value at most `1/3` if `value d ≤ 1/3`.
-/

namespace ShiQIP

open Arith

/-- The padding exponent of the perfect-complete description. -/
noncomputable def pipeExp (d : Desc) : ℕ := padExp (perfDesc (normDesc d)).numMsgs

/-- The compressed, perfectly complete three-message description. -/
noncomputable def compDesc (d : Desc) : Desc := compressR (pipeExp d) (padTo (perfDesc (normDesc d)))

/-- **The three-message description.** -/
noncomputable def threeDesc (d : Desc) : Desc := parRepeat (compDesc d) (repK (padM (pipeExp d)))

theorem compDesc_spec {d : Desc} (hd : d.Valid) :
    (compDesc d).Valid ∧ (compDesc d).HasSchedule 3 ∧
      (1 / 2 ≤ value d → value (compDesc d) = 1) ∧
      (value d ≤ 1 / 3 → value (compDesc d) ≤ 1 - repδ (padM (pipeExp d))) := by
  obtain ⟨hv1, hs1, hk1, hval1, -, -, -⟩ := normDesc_spec hd
  set d₁ := normDesc d
  set k₁ := d₁.numMsgs
  have hv2 := perfDesc_valid hv1 hs1 hk1
  have hs2 := hasSchedule_perfDesc hs1 hk1
  have hm2 : (perfDesc d₁).numMsgs = k₁ + 2 := Desc.numMsgs_of_hasSchedule hs2
  have hs3 : (padTo (perfDesc d₁)).HasSchedule (padM (pipeExp d)) := by
    have := hasSchedule_padTo hs2
    rwa [show padCount (k₁ + 2) = padM (pipeExp d) by rw [pipeExp, hm2]; rfl] at this
  have hv3 := padTo_valid hv2 hs2
  obtain ⟨hc1, hc2, hc3, hc4⟩ := compressR_spec (pipeExp d) _ hv3 hs3
  refine ⟨hc1, hc2, fun h => hc3 ?_, fun h => ?_⟩
  · rw [value_padTo]
    exact value_perfDesc_eq_one hv1 hs1 hk1 (by rw [hval1]; exact h)
  · have hsnd := perfDesc_sound hv1 hs1 hk1 (by rw [hval1]; exact h)
    have hM : 1 ≤ padM (pipeExp d) := le_trans (by norm_num) (three_le_padM _)
    have h1 : value (padTo (perfDesc d₁)) ≤ 1 - 1 / 36 := by rw [value_padTo]; linarith
    have := compressR_sound (r := pipeExp d) hv3 hs3 (ε := 1 / 36) (by norm_num) (by norm_num) h1
    unfold repδ
    rw [show (1 : ℝ) / (36 * (padM (pipeExp d) : ℝ) ^ 2) = 1 / 36 / (padM (pipeExp d) : ℝ) ^ 2 by
      rw [div_div]]
    exact this

/-- **The pipeline**: valid, three messages, perfect completeness above `2/3`, soundness `1/3`
below `1/3`. -/
theorem threeDesc_spec {d : Desc} (hd : d.Valid) :
    (threeDesc d).Valid ∧ (threeDesc d).HasSchedule 3 ∧
      (2 / 3 ≤ value d → value (threeDesc d) = 1) ∧ (value d ≤ 1 / 3 → value (threeDesc d) ≤ 1 / 3) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := compDesc_spec hd
  have hM : 1 ≤ padM (pipeExp d) := le_trans (by norm_num) (three_le_padM _)
  have hK : 1 ≤ repK (padM (pipeExp d)) := by unfold repK; nlinarith
  refine ⟨parRepeat_valid hc1 _, hasSchedule_parRepeat hc2 _, fun h => ?_, fun h => ?_⟩
  · rw [threeDesc, value_parRepeat hc1 hK, hc3 (by linarith), one_pow]
  · rw [threeDesc, value_parRepeat hc1 hK]
    exact repeated_soundness hM (value_mem_Icc _).1 (hc4 h)


/-! ## Resources of the pipeline -/

section Resources

theorem sum_range_list_map (f : ℕ → ℕ) : ∀ m, ((List.range m).map f).sum = ∑ j ∈ Finset.range m, f j
  | 0 => rfl
  | m + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_list_map f m,
      Finset.sum_range_succ]; simp

theorem gateCount_padDesc (d : Desc) (s : ℕ) : (padDesc d s).gateCount = d.gateCount := by
  simp [Desc.gateCount, padDesc]

theorem gateCount_appendV (d : Desc) : (appendV d).gateCount = d.gateCount := by
  simp [appendV, Desc.gateCount]

theorem gateCount_flagDesc (d : Desc) : (flagDesc d).gateCount = 1 := by
  simp only [Desc.gateCount, flagDesc, List.map_map]
  rw [sum_range_list_map, Finset.sum_eq_single d.numMsgs]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem length_swapAll_le (d : Desc) : (swapAll d).length ≤ 3 * d.totalWires := by
  unfold swapAll
  rw [List.length_flatMap, sum_range_list_map]
  calc ∑ j ∈ Finset.range d.totalWires, (if d.held d.numMsgs j = true then
        swapGates (bellShift d j) (bellMsgOff d + j) else []).length
      ≤ ∑ j ∈ Finset.range d.totalWires, 3 := Finset.sum_le_sum fun j _ => by
        split_ifs <;> simp [swapGates]
    _ = 3 * d.totalWires := by simp [mul_comm]

theorem gateCount_bellDesc_le (d : Desc) : (bellDesc d).gateCount ≤ d.gateCount + 3 * d.totalWires + 38 := by
  simp only [Desc.gateCount, bellDesc, List.map_map]
  rw [sum_range_list_map, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have hb : ∀ j, j < d.numMsgs → (bellBlock d j).length = bl d j := by
    intro j hj; simp [bellBlock, hj, bl]
  have h1 : ∑ j ∈ Finset.range d.numMsgs, (bellBlock d j).length =
      ∑ j ∈ Finset.range d.numMsgs, bl d j :=
    Finset.sum_congr rfl fun j hj => hb j (Finset.mem_range.mp hj)
  have h2 : (bellBlock d d.numMsgs).length = bl d d.numMsgs + 1 + (swapAll d).length := by
    simp [bellBlock, bl]; omega
  have h3 : (bellBlock d (d.numMsgs + 1)).length = 0 := by simp [bellBlock]
  have h4 : (bellBlock d (d.numMsgs + 2)).length = 37 := by
    simp [bellBlock, bellFinal, length_toffoliGates]
  have h5 := sum_bl_le d (d.numMsgs + 1)
  rw [Finset.sum_range_succ] at h5
  have h6 := length_swapAll_le d
  have hg : d.gateCount = (d.blocks.map List.length).sum := rfl
  simp only [Function.comp_apply]
  omega

end Resources


section Resources2

variable {d : Desc}

theorem totalWires_rejectDesc (hm : 1 ≤ d.numMsgs) : (rejectDesc d).totalWires = d.totalWires + 3 := by
  rw [rejectDesc, totalWires_pairDesc, sum_zw _ _ (by rw [segs_length, segs_length, numMsgs_flagDesc hm]),
    segs_sum, segs_sum, totalWires_flagDesc hm]
  ring

theorem gateCount_rejectDesc (hd : d.Valid) (hm : 1 ≤ d.numMsgs) (hlast : LastToVerifier d) :
    (rejectDesc d).gateCount = d.gateCount + 34 := by
  rw [rejectDesc, gateCount_pairDesc (numMsgs_flagDesc hm).symm hd (flagDesc_valid hd hm hlast),
    gateCount_flagDesc]

theorem hsize_normDesc (hd : d.Valid) : hsize (normDesc d) ≤ hsize d + 1 := by
  obtain ⟨-, -, -, -, h1, h2, h3⟩ := normDesc_spec hd
  unfold hsize; omega

theorem hsize_perfDesc {k : ℕ} (hd : d.Valid) (hs : d.HasSchedule k) (hk : 1 ≤ k) :
    hsize (perfDesc d) ≤ 93 * hsize d := by
  have hm := one_le_numMsgs_of_hasSchedule hs hk
  have hlast := lastToVerifier_of_hasSchedule hs hk
  have h1 := gateCount_bellDesc_le (rejectDesc d)
  rw [gateCount_rejectDesc hd hm hlast, totalWires_rejectDesc hm] at h1
  have h2 : (perfDesc d).totalWires = 2 * d.totalWires + 9 := by
    rw [totalWires_perfDesc, totalWires_rejectDesc hm]; ring
  have h3 : (perfDesc d).numMsgs = d.numMsgs + 2 := by
    rw [numMsgs_perfDesc, numMsgs_rejectDesc hm]
  have h4 : (perfDesc d).gateCount = (bellDesc (rejectDesc d)).gateCount := rfl
  unfold hsize
  omega

theorem hsize_padTo : hsize (padTo d) ≤ 5 * hsize d := by
  have h1 := numMsgs_padTo (d := d)
  have h2 := padCount_le d.numMsgs
  have h3 : (padTo d).gateCount = d.gateCount := gateCount_padDesc _ _
  have h4 := totalWires_padTo (d := d)
  unfold hsize
  omega

theorem hsize_parRepeat (hd : d.Valid) {k : ℕ} (hk : 1 ≤ k) : hsize (parRepeat d k) ≤ 38 * k * hsize d := by
  have h1 := gateCount_parRepeat hd hk
  have h2 := totalWires_parRepeat d hk
  have h3 := numMsgs_parRepeat d k
  unfold hsize
  rw [h1, h2, h3]
  have : 1 ≤ k * (d.gateCount + d.totalWires + d.numMsgs + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith [Nat.sub_le k 1]

/-- **The pipeline is polynomially bounded**: `hsize (threeDesc d) ≤ C (hsize d + 1) ^ 14`. -/
theorem hsize_threeDesc_le (hd : d.Valid) :
    hsize (threeDesc d) ≤ 38 * 72 * 189 ^ 2 * 94 ^ 11 * 465 * (hsize d + 1) ^ 14 := by
  obtain ⟨hv1, hs1, hk1, -, -, -, -⟩ := normDesc_spec hd
  set d₁ := normDesc d
  set d₂ := perfDesc d₁
  set H := hsize d + 1 with hH
  have hH1 : 1 ≤ H := by omega
  have e1 : hsize d₁ ≤ H := hsize_normDesc hd
  have e2 : hsize d₂ ≤ 93 * H := (hsize_perfDesc hv1 hs1 hk1).trans (by omega)
  have hv2 := perfDesc_valid hv1 hs1 hk1
  have hs2 := hasSchedule_perfDesc hs1 hk1
  have hm2' : d₂.numMsgs ≤ hsize d₂ := by unfold hsize; omega
  have hm2 : d₂.numMsgs ≤ 93 * H := by omega
  set r := pipeExp d
  have hs3 : (padTo d₂).HasSchedule (padM r) := by
    have := hasSchedule_padTo hs2
    rwa [show padCount (d₁.numMsgs + 2) = padM r by
      rw [show r = padExp d₂.numMsgs from rfl, Desc.numMsgs_of_hasSchedule hs2]; rfl] at this
  have hv3 := padTo_valid hv2 hs2
  have hM : padM r ≤ 2 * d₂.numMsgs + 3 := padCount_le _
  have h2r : 2 ^ r ≤ 94 * H := by
    have : 2 ^ (r + 1) + 1 ≤ 2 * d₂.numMsgs + 3 := hM
    rw [pow_succ] at this; omega
  have hpow : 2010 ^ r ≤ (94 * H) ^ 11 := by
    calc 2010 ^ r ≤ 2048 ^ r := Nat.pow_le_pow_left (by norm_num) r
      _ = (2 ^ r) ^ 11 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (94 * H) ^ 11 := Nat.pow_le_pow_left h2r 11
  have e3 : hsize (padTo d₂) ≤ 5 * (93 * H) := hsize_padTo.trans (by omega)
  have e4 : hsize (compDesc d) ≤ (94 * H) ^ 11 * (465 * H) := by
    calc hsize (compDesc d) ≤ 2010 ^ r * hsize (padTo d₂) := hsize_compressR_le r _ hs3
      _ ≤ (94 * H) ^ 11 * (465 * H) := Nat.mul_le_mul hpow (by omega)
  have hc1 := (compDesc_spec hd).1
  have hK1 : 1 ≤ repK (padM r) := by unfold repK; have := three_le_padM r; nlinarith
  have hK : repK (padM r) ≤ 72 * (189 * H) ^ 2 := by
    unfold repK
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  calc hsize (threeDesc d) ≤ 38 * repK (padM r) * hsize (compDesc d) := hsize_parRepeat hc1 hK1
    _ ≤ 38 * (72 * (189 * H) ^ 2) * ((94 * H) ^ 11 * (465 * H)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) e4
    _ = 38 * 72 * 189 ^ 2 * 94 ^ 11 * 465 * H ^ 14 := by ring

end Resources2

end ShiQIP
