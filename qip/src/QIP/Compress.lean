import QIP.Halve.Valid
import QIP.Arithmetic.Gap
import QIP.Arithmetic.Padding
import QIP.Arithmetic.Repetition


/-!
# Q32 — iterated semantic compression

A valid description with `M = 2 ^ (r + 1) + 1` messages (`M = padM r`) is halved `r` times
(`compressR`): message counts `2 ^ (r + 1) + 1 → 2 ^ r + 1 → ⋯ → 3`. For `r = 0` nothing is done.

* **`compressR_spec`**: the result is valid, follows the three-message schedule, is perfectly
  complete when the input is, and from soundness `1 - ε` (`ε ≤ 1`) has soundness `1 - ε / 4 ^ r`.
* **`compressR_sound`**: with `M = padM r`, soundness `1 - ε / M ^ 2` (`0 ≤ ε ≤ 1`).
-/

namespace ShiQIP

open Arith

/-- **`r` halving steps**, from `2 ^ (r + 1) + 1` messages to three. -/
def compressR : ℕ → Desc → Desc
  | 0, d => d
  | r + 1, d => compressR r (halveDesc d (2 ^ (r + 1)))

theorem compressR_zero (d : Desc) : compressR 0 d = d := rfl

theorem compressR_succ (r : ℕ) (d : Desc) : compressR (r + 1) d = compressR r (halveDesc d (2 ^ (r + 1))) := rfl

/-- **Iterated compression.** -/
theorem compressR_spec : ∀ (r : ℕ) (d : Desc), d.Valid → d.HasSchedule (padM r) →
    (compressR r d).Valid ∧ (compressR r d).HasSchedule 3 ∧ (value d = 1 → value (compressR r d) = 1) ∧
      ∀ ε : ℝ, ε ≤ 1 → value d ≤ 1 - ε → value (compressR r d) ≤ 1 - ε / 4 ^ r
  | 0, d, hd, hs => ⟨hd, hs, id, fun ε _ h => by rw [compressR_zero, pow_zero, div_one]; exact h⟩
  | r + 1, d, hd, hs => by
    obtain ⟨hv, hsch, hsnd, hcpl⟩ := halve_pow (r := r + 1) (by omega) hd hs
    obtain ⟨ih1, ih2, ih3, ih4⟩ := compressR_spec r (halveDesc d (2 ^ (r + 1))) hv hsch
    refine ⟨ih1, ih2, fun h => ih3 (hcpl h), fun ε hε h => ?_⟩
    have h1 : value (halveDesc d (2 ^ (r + 1))) ≤ 1 - ε / 4 :=
      hsnd.trans (halving_step hε h)
    have h2 := ih4 (ε / 4) (by linarith) h1
    rw [compressR_succ]
    calc value (compressR r (halveDesc d (2 ^ (r + 1)))) ≤ 1 - ε / 4 / 4 ^ r := h2
      _ = 1 - ε / 4 ^ (r + 1) := by rw [div_div, pow_succ, mul_comm]

/-- **Iterated compression, in terms of the padded message count** `M = padM r`. -/
theorem compressR_sound {r : ℕ} {d : Desc} (hd : d.Valid) (hs : d.HasSchedule (padM r)) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hv : value d ≤ 1 - ε) :
    value (compressR r d) ≤ 1 - ε / (padM r : ℝ) ^ 2 :=
  ((compressR_spec r d hd hs).2.2.2 ε h1 hv).trans (compressed_gap h0 r)


/-! ## Size recurrence -/

section Size

variable (d : Desc) (n : ℕ)

theorem sum_wd_le (L : ℕ) : ∑ j ∈ Finset.range L, wd d j ≤ d.communication := by
  have h : ∀ L, ∑ j ∈ Finset.range L, wd d j = ((d.msgs.take L).map Message.width).sum := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, List.take_add_one, List.map_append, List.sum_append]
      unfold wd Desc.msgWidth
      cases d.msgs[L]? <;> simp
  rw [h, Desc.communication]
  conv_rhs => rw [← List.take_append_drop L d.msgs]
  rw [List.map_append, List.sum_append]
  omega

theorem communication_le : d.communication ≤ d.totalWires := by
  rw [Desc.totalWires_eq]; omega

theorem held0_length_le : (held0 d).length ≤ d.totalWires := by
  unfold held0
  exact (List.length_filter_le _ _).trans (by simp)

theorem sum_hw_le (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, hw d n (k + 1) ≤ d.communication := by
  have h1 : ∀ k ∈ Finset.range n, hw d n (k + 1) ≤ wd d (n + 1 + k) + wd d (n - k) := by
    intro k _
    unfold hw
    rw [if_neg (by omega), show n + (k + 1) = n + 1 + k by omega, show n + 1 - (k + 1) = n - k by omega]
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have h2 : ∑ k ∈ Finset.range n, wd d (n + 1 + k) = ∑ j ∈ Finset.Ico (n + 1) (2 * n + 1), wd d j := by
    rw [Finset.sum_Ico_eq_sum_range, show 2 * n + 1 - (n + 1) = n by omega]
  have h3 : ∑ k ∈ Finset.range n, wd d (n - k) = ∑ j ∈ Finset.Ico 1 (n + 1), wd d j := by
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    congr 1; omega
  have h4 : ∑ j ∈ Finset.Ico 1 (n + 1), wd d j + ∑ j ∈ Finset.Ico (n + 1) (2 * n + 1), wd d j ≤
      ∑ j ∈ Finset.range (2 * n + 1), wd d j := by
    rw [Finset.sum_Ico_consecutive _ (by omega) (by omega), Finset.range_eq_Ico]
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left (by omega))
  calc ∑ k ∈ Finset.range n, hw d n (k + 1)
      ≤ ∑ k ∈ Finset.range n, (wd d (n + 1 + k) + wd d (n - k)) := Finset.sum_le_sum h1
    _ = _ := Finset.sum_add_distrib
    _ ≤ d.communication := by rw [h2, h3]; linarith [sum_wd_le d (2 * n + 1)]

/-- **Wire recurrence**: halving at most quadruples the wires, plus `4`. -/
theorem totalWires_halveDesc_le (hn : 1 ≤ n) : (halveDesc d n).totalWires ≤ 4 * d.totalWires + 4 := by
  rw [totalWires_halveDesc]
  have e : ∀ m, hOff d n m = hPriv d + ∑ k ∈ Finset.range m, (hw d n k + if k = 1 then 1 else 0) := by
    intro m
    induction m with
    | zero => simp [hOff]
    | succ m ih => rw [hOff_succ, ih, Finset.sum_range_succ]; ring
  rw [e, Finset.sum_range_succ', Finset.sum_add_distrib]
  have h1 := sum_hw_le d n hn
  have h2 : ∑ k ∈ Finset.range n, (if k + 1 = 1 then 1 else 0) ≤ 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    omega
  have h3 := held0_length_le d
  have h4 := communication_le d
  rw [show hw d n 0 = d.totalWires by simp [hw], if_neg (show (0 : ℕ) ≠ 1 by omega)]
  unfold hPriv
  omega

end Size


/-! ## Gate-count recurrence -/

section Gates

variable (d : Desc) (n : ℕ)

theorem length_swapRange (p q r : ℕ) : (swapRange p q r).length = 3 * r := by
  induction r with
  | zero => simp [swapRange]
  | succ r ih =>
    rw [swapRange, List.range_succ, List.flatMap_append, List.length_append, ← swapRange, ih]
    simp [swapGates]; ring

theorem length_swapMsg (k j : ℕ) : (swapMsg d n k j).length = 3 * wd d j := length_swapRange _ _ _

theorem length_onF_le (gs : List Gate) : (onF d gs).length ≤ 2 + 67 * gs.length := by
  have := length_ctrlGates_le (hCoin d) (hCa d) gs
  simp only [onF, List.length_append, List.length_singleton]; omega

theorem length_onB_le (gs : List Gate) : (onB d gs).length ≤ 67 * gs.length :=
  length_ctrlGates_le _ _ _

theorem length_ztGates : ∀ (S anc : List ℕ) (c t : ℕ), S.length ≤ anc.length →
    (ztGates c t S anc).length = 70 * S.length + 1
  | [], _, _, _, _ => by simp [ztGates]
  | _ :: _, [], _, _, h => by simp at h
  | s :: S, a :: anc, c, t, h => by
    simp only [ztGates, List.length_append, ncaGates, length_toffoliGates, List.length_cons]
    rw [length_ztGates S anc a t (by simp at h; omega)]
    simp only [List.length_nil]
    ring

/-- The gate count of block `j` of `d`. -/
def bl (j : ℕ) : ℕ := (d.blocks.getD j []).length

theorem sum_bl_le (L : ℕ) : ∑ j ∈ Finset.range L, bl d j ≤ d.gateCount := by
  have h : ∀ L, ∑ j ∈ Finset.range L, bl d j = ((d.blocks.take L).map List.length).sum := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, List.take_add_one, List.map_append, List.sum_append]
      unfold bl
      rw [List.getD_eq_getElem?_getD]
      cases d.blocks[L]? <;> simp
  rw [h, Desc.gateCount]
  conv_rhs => rw [← List.take_append_drop L d.blocks]
  rw [List.map_append, List.sum_append]
  omega

theorem bl_le (j : ℕ) : bl d j ≤ d.gateCount := by
  have := sum_bl_le d (j + 1)
  rw [Finset.sum_range_succ] at this
  omega

theorem wd_le (j : ℕ) : wd d j ≤ d.communication := by
  have := sum_wd_le d (j + 1)
  rw [Finset.sum_range_succ] at this
  omega

theorem length_adjB (j : ℕ) : (adjointGates (d.blocks.getD j [])).length ≤ 7 * bl d j :=
  length_adjointGates_le _

end Gates


section Gates2

variable (d : Desc) (n : ℕ)

theorem sum_comp_le {s : Finset ℕ} {f : ℕ → ℕ} (hf : Set.InjOn f s) {L : ℕ} (hL : ∀ k ∈ s, f k < L)
    (g : ℕ → ℕ) : ∑ k ∈ s, g (f k) ≤ ∑ j ∈ Finset.range L, g j := by
  rw [← Finset.sum_image hf]
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  simp only [Finset.mem_image] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  exact Finset.mem_range.mpr (hL k hk)

theorem length_ite_le (c : Prop) [Decidable c] (gs : List Gate) : (if c then gs else []).length ≤ gs.length := by
  split_ifs <;> simp

theorem hBlock_one_le (_hn : 1 ≤ n) : (hBlock d n 1).length ≤
    3 * d.totalWires + 4 + 201 * wd d (n + 1) + 469 * bl d (n + 1) + 201 * wd d n := by
  rw [hBlock, if_neg (by omega), if_pos rfl]
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h1 := length_onF_le d (swapMsg d n 1 (n + 1))
  have h2 := length_onB_le d (adjointGates (d.blocks.getD (n + 1) []) ++ swapMsg d n 1 n)
  have h3 := length_adjB d (n + 1)
  rw [length_swapMsg] at h1
  rw [List.length_append, length_swapMsg] at h2
  have h4 : ((List.range d.totalWires).flatMap fun x => swapGates (hOff d n 0 + x) x).length = 3 * d.totalWires := by
    rw [show ((List.range d.totalWires).flatMap fun x => swapGates (hOff d n 0 + x) x) = swap0 d n from rfl,
      swap0_eq, length_swapRange]
  omega

theorem hBlock_mid_le {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) : (hBlock d n k).length ≤
    2 + 201 * wd d (n + k - 1) + 67 * bl d (n + k) + 201 * wd d (n + k) +
      201 * wd d (n + 2 - k) + 469 * bl d (n + 2 - k) + 201 * wd d (n + 1 - k) := by
  rw [hBlock, if_neg (by omega), if_neg (by omega), if_pos hkn, List.length_append]
  have h1 := length_onF_le d (fwdStep d n k)
  have h2 := length_onB_le d (bwdStep d n k)
  have h3 := length_adjB d (n + 2 - k)
  have a1 := length_ite_le ((k - 1) % 2 = 0) (swapMsg d n (k - 1) (n + k - 1))
  have a2 := length_ite_le (k % 2 = 1) (swapMsg d n k (n + k))
  have a3 := length_ite_le ((k - 1) % 2 = 0) (swapMsg d n (k - 1) (n + 2 - k))
  have a4 := length_ite_le (k % 2 = 1) (swapMsg d n k (n + 1 - k))
  simp only [length_swapMsg] at a1 a2 a3 a4
  have hf : (fwdStep d n k).length = (if (k - 1) % 2 = 0 then swapMsg d n (k - 1) (n + k - 1) else []).length +
      bl d (n + k) + (if k % 2 = 1 then swapMsg d n k (n + k) else []).length := by
    simp only [fwdStep, List.length_append]; rfl
  have hb : (bwdStep d n k).length = (if (k - 1) % 2 = 0 then swapMsg d n (k - 1) (n + 2 - k) else []).length +
      (adjointGates (d.blocks.getD (n + 2 - k) [])).length +
        (if k % 2 = 1 then swapMsg d n k (n + 1 - k) else []).length := by
    simp only [bwdStep, List.length_append]
  omega

theorem hBlock_last_le (hn : 1 ≤ n) : (hBlock d n (n + 1)).length ≤
    70 * d.totalWires + 70 + 201 * wd d (2 * n) + 67 * bl d (2 * n + 1) +
      201 * wd d 1 + 469 * bl d 1 + 469 * bl d 0 := by
  rw [hBlock_last hn, List.length_append, List.length_append]
  have h1 := length_onF_le d (finF d n ++ [Gate.cnot d.out (hOut d)])
  have h2 := length_onB_le d (finB d n)
  have h3 := length_adjB d 1
  have h4 := length_adjB d 0
  have h5 := length_ztGates (held0 d) (hAnc d) (hCoin d) (hOut d) (by simp [hAnc])
  have h6 := held0_length_le d
  have hf : (finF d n ++ [Gate.cnot d.out (hOut d)]).length = 3 * wd d (2 * n) + bl d (2 * n + 1) + 1 := by
    simp only [finF, List.length_append, length_swapMsg, List.length_singleton]; rfl
  have hb : (finB d n).length = 3 * wd d 1 + (adjointGates (d.blocks.getD 1 [])).length +
      (adjointGates (d.blocks.getD 0 [])).length := by
    simp only [finB, List.length_append, length_swapMsg]
  omega

/-- **Gate recurrence**: halving multiplies the gate count by a constant, plus terms linear in the
wires and the message count. -/
theorem gateCount_halveDesc_le (hn : 1 ≤ n) :
    (halveDesc d n).gateCount ≤ 2010 * d.gateCount + 1700 * d.totalWires + 2 * n + 80 := by
  have hgc : (halveDesc d n).gateCount = ∑ k ∈ Finset.range (n + 2), (hBlock d n k).length := by
    simp only [Desc.gateCount, halveDesc, List.map_map]
    generalize n + 2 = m
    induction m with
    | zero => simp
    | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [hgc, Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _ (show 2 ≤ n + 1 by omega)]
  have h0 : (hBlock d n 0).length = 0 := by simp [hBlock]
  have hr2 : ∑ k ∈ Finset.range 2, (hBlock d n k).length = (hBlock d n 0).length + (hBlock d n 1).length := by
    simp [Finset.sum_range_succ]
  have h1 := hBlock_one_le d n hn
  have hl := hBlock_last_le d n hn
  have hm : ∑ k ∈ Finset.Ico 2 (n + 1), (hBlock d n k).length ≤ ∑ k ∈ Finset.Ico 2 (n + 1),
      (2 + 201 * wd d (n + k - 1) + 67 * bl d (n + k) + 201 * wd d (n + k) +
        201 * wd d (n + 2 - k) + 469 * bl d (n + 2 - k) + 201 * wd d (n + 1 - k)) :=
    Finset.sum_le_sum fun k hk => by
      rw [Finset.mem_Ico] at hk
      exact hBlock_mid_le d n (by omega) (by omega)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hm
  have inj : ∀ (f : ℕ → ℕ), (∀ a b, 2 ≤ a → a < n + 1 → 2 ≤ b → b < n + 1 → f a = f b → a = b) →
      Set.InjOn f (Finset.Ico 2 (n + 1)) := by
    intro f hf a ha b hb e
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hf a b ha.1 ha.2 hb.1 hb.2 e
  have s1 := (sum_comp_le (inj (fun k => n + k - 1) (fun a b _ _ _ _ e => by omega))
    (L := 2 * n + 2) (fun k hk => by rw [Finset.mem_Ico] at hk; omega) (wd d)).trans (sum_wd_le d _)
  have s2 := (sum_comp_le (inj (fun k => n + k) (fun a b _ _ _ _ e => by omega))
    (L := 2 * n + 2) (fun k hk => by rw [Finset.mem_Ico] at hk; omega) (bl d)).trans (sum_bl_le d _)
  have s3 := (sum_comp_le (inj (fun k => n + k) (fun a b _ _ _ _ e => by omega))
    (L := 2 * n + 2) (fun k hk => by rw [Finset.mem_Ico] at hk; omega) (wd d)).trans (sum_wd_le d _)
  have s4 := (sum_comp_le (inj (fun k => n + 2 - k) (fun a b _ _ _ _ e => by omega))
    (L := 2 * n + 2) (fun k hk => by rw [Finset.mem_Ico] at hk; omega) (wd d)).trans (sum_wd_le d _)
  have s5 := (sum_comp_le (inj (fun k => n + 2 - k) (fun a b _ _ _ _ e => by omega))
    (L := 2 * n + 2) (fun k hk => by rw [Finset.mem_Ico] at hk; omega) (bl d)).trans (sum_bl_le d _)
  have s6 := (sum_comp_le (inj (fun k => n + 1 - k) (fun a b _ _ _ _ e => by omega))
    (L := 2 * n + 2) (fun k hk => by rw [Finset.mem_Ico] at hk; omega) (wd d)).trans (sum_wd_le d _)
  have hc := communication_le d
  have w1 := wd_le d (n + 1); have w2 := wd_le d n; have w3 := wd_le d (2 * n); have w4 := wd_le d 1
  have b1 := bl_le d (n + 1); have b2 := bl_le d (2 * n + 1); have b3 := bl_le d 1; have b4 := bl_le d 0
  omega

end Gates2


/-! ## The size recurrence of compression -/

section CompressSize

/-- A size measure: gates, wires and messages. -/
def hsize (d : Desc) : ℕ := d.gateCount + d.totalWires + d.numMsgs + 1

/-- **One halving step multiplies the size by at most `2010`.** -/
theorem hsize_halveDesc_le (d : Desc) {n : ℕ} (hn : 1 ≤ n) (hm : n ≤ d.numMsgs) :
    hsize (halveDesc d n) ≤ 2010 * hsize d := by
  have h1 := gateCount_halveDesc_le d n hn
  have h2 := totalWires_halveDesc_le d n hn
  have h3 := numMsgs_halveDesc d n
  unfold hsize
  omega

/-- **The size of the compressed description**: at most `2010 ^ r` times the original. -/
theorem hsize_compressR_le : ∀ (r : ℕ) (d : Desc), d.HasSchedule (padM r) →
    hsize (compressR r d) ≤ 2010 ^ r * hsize d
  | 0, d, _ => by simp [compressR]
  | r + 1, d, hs => by
    have hm := Desc.numMsgs_of_hasSchedule hs
    have hsch : (halveDesc d (2 ^ (r + 1))).HasSchedule (padM r) :=
      hasSchedule_halveDesc (by rw [pow_succ]; omega)
    have h1 := hsize_compressR_le r (halveDesc d (2 ^ (r + 1))) hsch
    have h2 := hsize_halveDesc_le d (n := 2 ^ (r + 1)) Nat.one_le_two_pow
      (by rw [hm, padM, pow_succ 2 (r + 1)]; omega)
    rw [compressR_succ]
    calc hsize (compressR r (halveDesc d (2 ^ (r + 1)))) ≤ 2010 ^ r * hsize (halveDesc d (2 ^ (r + 1))) := h1
      _ ≤ 2010 ^ r * (2010 * hsize d) := Nat.mul_le_mul_left _ h2
      _ = 2010 ^ (r + 1) * hsize d := by ring

end CompressSize

end ShiQIP
