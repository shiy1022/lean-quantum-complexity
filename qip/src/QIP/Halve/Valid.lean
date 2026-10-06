import QIP.Halve.Complete
import QIP.PadMessages


/-!
# Q31 — the halved description is valid and has `n + 1` messages
-/

namespace ShiQIP

/-! ## Well-formed gate lists -/

theorem okBool_of_wires {ok : ℕ → Bool} {g : Gate} (h1 : ∀ w ∈ g.wires, ok w = true)
    (h2 : ∀ i j, g = .cnot i j → i ≠ j) : g.okBool ok = true := by
  cases g with
  | cnot i j =>
    simp only [Gate.okBool, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨h1 i (by simp [Gate.wires]), h1 j (by simp [Gate.wires])⟩, h2 i j rfl⟩
  | _ i => exact h1 i (by simp [Gate.wires])

theorem wires_of_okBool {ok : ℕ → Bool} {g : Gate} (h : g.okBool ok = true) : ∀ w ∈ g.wires, ok w = true := by
  cases g with
  | cnot i j =>
    simp only [Gate.okBool, Bool.and_eq_true] at h
    intro w hw; simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h.1.1
    · exact h.1.2
  | _ i => intro w hw; simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hw; subst hw; exact h

theorem cnot_ne_of_okBool {ok : ℕ → Bool} {i j : ℕ} (h : (Gate.cnot i j).okBool ok = true) : i ≠ j := by
  simp only [Gate.okBool, Bool.and_eq_true, bne_iff_ne] at h; exact h.2

theorem okBool_mono {ok ok' : ℕ → Bool} (hok : ∀ w, ok w = true → ok' w = true) {g : Gate}
    (h : g.okBool ok = true) : g.okBool ok' = true :=
  okBool_of_wires (fun w hw => hok w (wires_of_okBool h w hw)) (fun i j e => by subst e; exact cnot_ne_of_okBool h)

theorem okBool_swapGates {ok : ℕ → Bool} {p q : ℕ} (hp : ok p = true) (hq : ok q = true) (hpq : p ≠ q) :
    ∀ g ∈ swapGates p q, g.okBool ok = true := by
  intro g hg
  simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp [Gate.okBool, hp, hq, hpq, Ne.symm hpq]

theorem okBool_swapRange {ok : ℕ → Bool} {p q r : ℕ} (hp : ∀ i < r, ok (p + i) = true)
    (hq : ∀ i < r, ok (q + i) = true) (hpq : p ≠ q) : ∀ g ∈ swapRange p q r, g.okBool ok = true := by
  intro g hg
  simp only [swapRange, List.mem_flatMap, List.mem_range] at hg
  obtain ⟨i, hi, hg⟩ := hg
  exact okBool_swapGates (hp i hi) (hq i hi) (by omega) g hg

theorem okBool_ctrlGates {ok : ℕ → Bool} {c a : ℕ} (hc : ok c = true) (ha : ok a = true) (hca : c ≠ a)
    {gs : List Gate} (hgs : ∀ g ∈ gs, g.okBool ok = true ∧ c ∉ g.wires ∧ a ∉ g.wires) :
    ∀ g ∈ ctrlGates c a gs, g.okBool ok = true := by
  intro g hg
  simp only [ctrlGates, List.mem_flatMap] at hg
  obtain ⟨g₀, hg₀, hg⟩ := hg
  obtain ⟨hok, hcw, haw⟩ := hgs g₀ hg₀
  cases g₀ with
  | x i =>
    simp only [ctrlGate, List.mem_singleton] at hg; subst hg
    have hi := wires_of_okBool hok i (by simp [Gate.wires])
    have : c ≠ i := fun e => hcw (by simp [Gate.wires, e])
    simp [Gate.okBool, hc, hi, this]
  | cnot i j =>
    simp only [ctrlGate] at hg
    have hi := wires_of_okBool hok i (by simp [Gate.wires])
    have hj := wires_of_okBool hok j (by simp [Gate.wires])
    exact okBool_toffoliGates hc hi hj (fun e => hcw (by simp [Gate.wires, e]))
      (fun e => hcw (by simp [Gate.wires, e])) (cnot_ne_of_okBool hok) g hg
  | s i =>
    have hi := wires_of_okBool hok i (by simp [Gate.wires])
    have : c ≠ i := fun e => hcw (by simp [Gate.wires, e])
    simp only [ctrlGate, tdgGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at hg
    rcases hg with ((rfl | rfl | rfl) | ⟨_, rfl⟩) | rfl <;> simp [Gate.okBool, hc, hi, this]
  | t i =>
    have hi := wires_of_okBool hok i (by simp [Gate.wires])
    simp only [ctrlGate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (h | rfl) | h
    · exact okBool_toffoliGates hc hi ha (fun e => hcw (by simp [Gate.wires, e])) hca
        (fun e => haw (by simp [Gate.wires, e])) g h
    · simp [Gate.okBool, ha]
    · exact okBool_toffoliGates hc hi ha (fun e => hcw (by simp [Gate.wires, e])) hca
        (fun e => haw (by simp [Gate.wires, e])) g h
  | h i =>
    have hi := wires_of_okBool hok i (by simp [Gate.wires])
    have : c ≠ i := fun e => hcw (by simp [Gate.wires, e])
    simp only [ctrlGate, sdgGates, tdgGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at hg
    rcases hg with ((⟨_, rfl⟩ | rfl) | ⟨_, rfl⟩) | rfl | rfl | rfl | rfl <;> simp [Gate.okBool, hc, hi, this]

theorem okBool_ztGates {ok : ℕ → Bool} : ∀ (S anc : List ℕ) (c t : ℕ), (c :: t :: (S ++ anc)).Nodup →
    (∀ w ∈ c :: t :: (S ++ anc), ok w = true) → ∀ g ∈ ztGates c t S anc, g.okBool ok = true
  | [], anc, c, t, hnd, hok, g, hg => by
    simp only [ztGates, List.mem_singleton] at hg; subst hg
    have hct : c ≠ t := by intro e; rw [e] at hnd; simp at hnd
    simp [Gate.okBool, hok c (by simp), hok t (by simp), hct]
  | s :: S, [], _, _, _, _, g, hg => by simp [ztGates] at hg
  | s :: S, a :: anc, c, t, hnd, hok, g, hg => by
    have hnd' := hnd
    simp only [List.cons_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or,
      List.nodup_append] at hnd'
    have hcs : c ≠ s := by tauto
    have hca : c ≠ a := by tauto
    have hsa : s ≠ a := by tauto
    have hrec : (a :: t :: (S ++ anc)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or, List.nodup_append]
      refine ⟨⟨fun e => by tauto, by tauto, by tauto⟩, ⟨by tauto, by tauto⟩, by tauto, by tauto, ?_⟩
      intro x hx y' hy'
      exact hnd'.2.2.2.2.2 x hx y' (Or.inr hy')
    have hc := hok c (by simp)
    have hs := hok s (by simp)
    have ha := hok a (by simp)
    simp only [ztGates, List.mem_append] at hg
    have hnca : ∀ g ∈ ncaGates c s a, g.okBool ok = true := by
      intro g hg
      simp only [ncaGates, List.mem_append, List.mem_singleton] at hg
      rcases hg with (rfl | h) | rfl
      · simp [Gate.okBool, hs]
      · exact okBool_toffoliGates hc hs ha hcs hca hsa g h
      · simp [Gate.okBool, hs]
    rcases hg with (h | h) | h
    · exact hnca g h
    · exact okBool_ztGates S anc a t hrec (fun w hw => hok w (by
        simp only [List.mem_cons, List.mem_append] at hw ⊢; tauto)) g h
    · exact hnca g h


/-! ## Wires held by the halved verifier -/

section Held

variable {d : Desc} {n : ℕ}

theorem held_halve_priv (k : ℕ) {w : ℕ} (hw : w < hPriv d) : (halveDesc d n).held k w = true := by
  simp [Desc.held, halveDesc, hw]

theorem held_halve_msg {k i w : ℕ} (hi : i ≤ n) (hw1 : hOff d n i ≤ w) (hw2 : w < hOff d n (i + 1))
    (hdir : (i % 2 = 0 ∧ i < k) ∨ (i % 2 = 1 ∧ k ≤ i)) : (halveDesc d n).held k w = true := by
  have hlt : w < (halveDesc d n).totalWires := by
    rw [totalWires_halveDesc]; have := hOff_mono d n (show i + 1 ≤ n + 1 by omega); omega
  have := (held_iff (halveDesc d n) k ⟨w, hlt⟩).mpr (Or.inr ⟨i, by
    rw [inReg_halve_iff hi]; rw [hOff_succ] at hw2; exact ⟨hw1, hw2⟩, by
    rw [dir_halveDesc d n i hi]
    rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1]; simp [dirOk, h2]
    · rw [if_neg (by omega)]; simp [dirOk, h2]⟩)
  exact this

/-- Gates well formed for block `b` and avoiding the coin and the control ancilla. -/
def GoodAt (d : Desc) (n b : ℕ) (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.okBool ((halveDesc d n).held b) = true ∧ hCoin d ∉ g.wires ∧ hCa d ∉ g.wires

theorem GoodAt.append {b : ℕ} {gs gs' : List Gate} (h : GoodAt d n b gs) (h' : GoodAt d n b gs') :
    GoodAt d n b (gs ++ gs') := fun g hg => by
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · exact h' g hg

theorem goodAt_nil {b : ℕ} : GoodAt d n b [] := fun _ h => absurd h List.not_mem_nil

theorem goodAt_ite {b : ℕ} (c : Prop) [Decidable c] {gs : List Gate} (h : c → GoodAt d n b gs) :
    GoodAt d n b (if c then gs else []) := by
  split_ifs with hc
  · exact h hc
  · exact goodAt_nil

theorem goodAt_dBlock (hd : d.Valid) (b j : ℕ) : GoodAt d n b (d.blocks.getD j []) := by
  intro g hg
  have hsome := hd.toInstr?_isSome j g hg
  have hw := wires_lt_of_isSome hsome
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  refine ⟨okBool_mono (ok := fun w => decide (w < d.totalWires)) (fun w h => held_halve_priv b (by
    simp at h; omega)) ((Gate.toInstr?_isSome_iff _ _).mp hsome), fun h => ?_, fun h => ?_⟩
  · have := hw _ h; unfold hCoin at this; omega
  · have := hw _ h; unfold hCa at this; omega

theorem inv_wires_okBool {g g' : Gate} (h : g' ∈ Gate.inv g) :
    g'.wires = g.wires ∧ ∀ ok, g'.okBool ok = g.okBool ok := by
  cases g with
  | h i => simp only [Gate.inv, List.mem_singleton] at h; subst h; exact ⟨rfl, fun _ => rfl⟩
  | s i => simp only [Gate.inv, List.mem_cons, List.not_mem_nil, or_false, or_self] at h; subst h
           exact ⟨rfl, fun _ => rfl⟩
  | t i => rw [Gate.inv, List.mem_replicate] at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, fun _ => rfl⟩
  | x i => simp only [Gate.inv, List.mem_singleton] at h; subst h; exact ⟨rfl, fun _ => rfl⟩
  | cnot i j => simp only [Gate.inv, List.mem_singleton] at h; subst h; exact ⟨rfl, fun _ => rfl⟩

theorem goodAt_adj {b : ℕ} {gs : List Gate} (h : GoodAt d n b gs) : GoodAt d n b (adjointGates gs) := by
  intro g' hg'
  simp only [adjointGates, List.mem_flatten, List.mem_map, List.mem_reverse] at hg'
  obtain ⟨l, ⟨g, hg, rfl⟩, hgl⟩ := hg'
  obtain ⟨hw, hok⟩ := inv_wires_okBool hgl
  obtain ⟨h1, h2, h3⟩ := h g hg
  exact ⟨by rw [hok]; exact h1, by rw [hw]; exact h2, by rw [hw]; exact h3⟩

theorem goodAt_swapMsg {b i j : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) (hj : wd d j ≤ hw d n i)
    (hdir : (i % 2 = 0 ∧ i < b) ∨ (i % 2 = 1 ∧ b ≤ i)) : GoodAt d n b (swapMsg d n i j) := by
  intro g hg
  have hA := avoid_swapMsg (d := d) (n := n) hi1 hin hj g hg
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have h1 := msgOffset_add_width_le d j
  have h2 := hPay_ge (d := d) (n := n) i
  have h3 : hPay d n i + wd d j ≤ hOff d n (i + 1) := by
    rw [hOff_succ]; unfold hPay; split_ifs <;> omega
  refine ⟨okBool_swapRange (fun t ht => held_halve_msg hin (by unfold hPay; split_ifs <;> omega)
    (by omega) hdir) (fun t ht => held_halve_priv b (by unfold wd at *; omega)) (by unfold wd at *; omega) g hg,
    hA.2.1, hA.2.2⟩

theorem okBool_onF {b : ℕ} {gs : List Gate} (h : GoodAt d n b gs) :
    ∀ g ∈ onF d gs, g.okBool ((halveDesc d n).held b) = true := by
  have hc := held_halve_priv (d := d) (n := n) b (show hCoin d < hPriv d by unfold hCoin hPriv; omega)
  have ha := held_halve_priv (d := d) (n := n) b (show hCa d < hPriv d by unfold hCa hPriv; omega)
  intro g hg
  simp only [onF, List.mem_append, List.mem_singleton] at hg
  rcases hg with (rfl | hg) | rfl
  · simpa [Gate.okBool] using hc
  · exact okBool_ctrlGates hc ha (by unfold hCoin hCa; omega) h g hg
  · simpa [Gate.okBool] using hc

theorem okBool_onB {b : ℕ} {gs : List Gate} (h : GoodAt d n b gs) :
    ∀ g ∈ onB d gs, g.okBool ((halveDesc d n).held b) = true := by
  have hc := held_halve_priv (d := d) (n := n) b (show hCoin d < hPriv d by unfold hCoin hPriv; omega)
  have ha := held_halve_priv (d := d) (n := n) b (show hCa d < hPriv d by unfold hCa hPriv; omega)
  exact okBool_ctrlGates hc ha (by unfold hCoin hCa; omega) h

end Held


/-! ## Validity and schedule -/

section Valid

variable {d : Desc} {n : ℕ}

/-- **The halved description follows the standard `(n + 1)`-message schedule.** -/
theorem hasSchedule_halveDesc (hne : n % 2 = 0) : (halveDesc d n).HasSchedule (n + 1) := by
  unfold Desc.HasSchedule
  apply List.ext_getElem
  · simp [halveDesc, hMsgs, stdSchedule]
  · intro i h1 h2
    simp only [halveDesc, hMsgs, stdSchedule, List.map_map, List.getElem_map, List.getElem_range,
      Function.comp_apply]
    have hi : i < n + 1 := by simpa [halveDesc, hMsgs] using h1
    by_cases h : i % 2 = 0
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem nodup_zt_nat : (hCoin d :: hOut d :: (held0 d ++ hAnc d)).Nodup := by
  have h1 : (held0 d).Nodup := (List.nodup_range).filter _
  have h2 : (hAnc d).Nodup := (List.nodup_range).map (fun a b h => by omega)
  have hS : ∀ w ∈ held0 d, w < d.totalWires := fun w h => by
    simp only [held0, List.mem_filter, List.mem_range] at h; exact h.1
  have hA : ∀ w ∈ hAnc d, d.totalWires + 3 ≤ w := fun w h => (mem_hAnc.mp h).1
  simp only [hCoin, hOut, List.nodup_cons, List.mem_cons, List.mem_append, not_or]
  refine ⟨⟨by omega, fun h => by have := hS _ h; omega, fun h => by have := hA _ h; omega⟩,
    ⟨fun h => by have := hS _ h; omega, fun h => by have := hA _ h; omega⟩,
    List.nodup_append.mpr ⟨h1, h2, fun a ha b hb e => ?_⟩⟩
  have := hS a ha; have := hA b hb; omega

/-- **The halved description is valid.** -/
theorem halveDesc_valid (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) : (halveDesc d n).Valid := by
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have hout := out_lt_W hd
  unfold Desc.Valid Desc.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨?_, alternates_of_dirs (hasSchedule_halveDesc hne)⟩, ?_⟩, ?_⟩
  · show hOut d < hPriv d; unfold hOut; omega
  · simp [halveDesc, hMsgs]
  refine blocksOkFrom_of _ 0 fun i g hg => ?_
  rw [zero_add]
  by_cases hi : i ≤ n + 1
  swap
  · rw [List.getD_eq_default _ _ (by simp [halveDesc]; omega)] at hg
    exact absurd hg List.not_mem_nil
  rw [blocks_getD_halve hi] at hg
  -- the four kinds of blocks
  by_cases h0 : i = 0
  · subst h0; simp [hBlock] at hg
  by_cases h1 : i = 1
  · subst h1
    rw [hBlock, if_neg (by omega), if_pos rfl] at hg
    simp only [List.mem_append] at hg
    rcases hg with ((hg | hg) | hg) | hg
    · rw [← swap0, swap0_eq] at hg
      refine okBool_swapRange (fun t ht => held_halve_msg (i := 0) (by omega) (by simp [hOff]) ?_
        (Or.inl ⟨rfl, by omega⟩)) (fun t ht => held_halve_priv 1 (by omega)) (by omega) g hg
      have : hOff d n (0 + 1) = hPriv d + d.totalWires := by rw [hOff_succ]; simp [hOff, hw]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      have hco := held_halve_priv (d := d) (n := n) 1 (show hCoin d < hPriv d by unfold hCoin; omega)
      have hcp := held_halve_msg (d := d) (n := n) (k := 1) (i := 1) (w := hOff d n 1) hn le_rfl
        (by have := hOff_succ d n 1; simp only [if_true] at this; omega) (Or.inr ⟨rfl, le_rfl⟩)
      have hne' : hCoin d ≠ hOff d n 1 := by have := hPriv_le_hOff d n 1; unfold hCoin; omega
      rcases hg with rfl | rfl
      · simpa [Gate.okBool] using hco
      · simp [Gate.okBool, hco, hcp, hne']
    · exact okBool_onF (goodAt_swapMsg le_rfl hn (wd_le_hw_fwd le_rfl) (Or.inr ⟨rfl, le_rfl⟩)) g hg
    · refine okBool_onB ((goodAt_adj (goodAt_dBlock hd 1 (n + 1))).append
        (goodAt_swapMsg le_rfl hn (by simpa using wd_le_hw_bwd (d := d) (n := n) (k := 1) le_rfl)
          (Or.inr ⟨rfl, le_rfl⟩))) g hg
  by_cases hmid : i ≤ n
  · rw [hBlock, if_neg h0, if_neg h1, if_pos hmid] at hg
    rcases List.mem_append.mp hg with hg | hg
    · refine okBool_onF (((goodAt_ite _ fun hc => goodAt_swapMsg (i := i - 1) (by omega) (by omega)
        (show wd d (n + i - 1) ≤ hw d n (i - 1) by
          rw [show n + i - 1 = n + (i - 1) by omega]; exact wd_le_hw_fwd (by omega))
          (Or.inl ⟨hc, by omega⟩)).append
        (goodAt_dBlock hd i (n + i))).append (goodAt_ite _ fun hc => goodAt_swapMsg (i := i) (by omega) hmid
          (wd_le_hw_fwd (by omega)) (Or.inr ⟨hc, le_rfl⟩))) g hg
    · refine okBool_onB (((goodAt_ite _ fun hc => goodAt_swapMsg (i := i - 1) (by omega) (by omega)
        (show wd d (n + 2 - i) ≤ hw d n (i - 1) by
          rw [show n + 2 - i = n + 1 - (i - 1) by omega]; exact wd_le_hw_bwd (by omega))
          (Or.inl ⟨hc, by omega⟩)).append
        (goodAt_adj (goodAt_dBlock hd i (n + 2 - i)))).append (goodAt_ite _ fun hc => goodAt_swapMsg (i := i)
          (by omega) hmid (wd_le_hw_bwd (by omega)) (Or.inr ⟨hc, le_rfl⟩))) g hg
  -- the final block
  obtain rfl : i = n + 1 := by omega
  rw [hBlock_last hn] at hg
  simp only [List.mem_append] at hg
  have hsw1 : GoodAt d n (n + 1) (swapMsg d n n (2 * n)) := goodAt_swapMsg hn le_rfl
    (by rw [show 2 * n = n + n by omega]; exact wd_le_hw_fwd hn) (Or.inl ⟨hne, by omega⟩)
  have hsw2 : GoodAt d n (n + 1) (swapMsg d n n 1) := goodAt_swapMsg hn le_rfl
    (by have := wd_le_hw_bwd (d := d) (n := n) (k := n) hn; rwa [show n + 1 - n = 1 by omega] at this)
    (Or.inl ⟨hne, by omega⟩)
  have hcn : GoodAt d n (n + 1) [Gate.cnot d.out (hOut d)] := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    refine ⟨?_, ?_, ?_⟩
    · simp only [Gate.okBool, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨⟨held_halve_priv _ (by omega), held_halve_priv _ (by unfold hOut; omega)⟩, by unfold hOut; omega⟩
    · simp [Gate.wires, hCoin, hOut]; omega
    · simp [Gate.wires, hCa, hOut]; omega
  rcases hg with (hg | hg) | hg
  · exact okBool_onF ((hsw1.append (goodAt_dBlock hd _ _)).append hcn) g hg
  · exact okBool_onB ((hsw2.append (goodAt_adj (goodAt_dBlock hd _ _))).append
      (goodAt_adj (goodAt_dBlock hd _ _))) g hg
  · refine okBool_ztGates _ _ _ _ nodup_zt_nat (fun w hw => held_halve_priv _ ?_) g hg
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | rfl | hw | hw
    · unfold hCoin; omega
    · unfold hOut; omega
    · simp only [held0, List.mem_filter, List.mem_range] at hw; omega
    · exact (mem_hAnc.mp hw).2

end Valid


/-! ## One halving step -/

section Spec

variable {d : Desc}

/-- **One halving step** (Q31): from `2n + 1` messages (`n` even, `n ≥ 1`) to `n + 1`, valid,
perfectly complete when `d` is, and `value ≤ (1 + √(value d)) / 2`. -/
theorem halve_spec {n : ℕ} (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hsch : d.HasSchedule (2 * n + 1)) :
    (halveDesc d n).Valid ∧ (halveDesc d n).HasSchedule (n + 1) ∧
      value (halveDesc d n) ≤ (1 + Real.sqrt (value d)) / 2 ∧
      (value d = 1 → value (halveDesc d n) = 1) :=
  ⟨halveDesc_valid hd hn hne, hasSchedule_halveDesc hne,
    value_halve_le hd hn hne (Desc.numMsgs_of_hasSchedule hsch),
    value_halve_eq_one hd hn hne hsch⟩

/-- **Halving `2^(r+1) + 1` messages to `2^r + 1`** (`r ≥ 1`). -/
theorem halve_pow {r : ℕ} (hr : 1 ≤ r) (hd : d.Valid) (hsch : d.HasSchedule (2 ^ (r + 1) + 1)) :
    (halveDesc d (2 ^ r)).Valid ∧ (halveDesc d (2 ^ r)).HasSchedule (2 ^ r + 1) ∧
      value (halveDesc d (2 ^ r)) ≤ (1 + Real.sqrt (value d)) / 2 ∧
      (value d = 1 → value (halveDesc d (2 ^ r)) = 1) := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h2 : 2 ^ r % 2 = 0 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [pow_succ]; omega
  have h3 : 2 ^ (r + 1) + 1 = 2 * 2 ^ r + 1 := by rw [pow_succ]; ring
  rw [h3] at hsch
  exact halve_spec hd h1 h2 hsch

/-- **The five-to-three case.** -/
theorem halve_five_to_three (hd : d.Valid) (hsch : d.HasSchedule 5) :
    (halveDesc d 2).Valid ∧ (halveDesc d 2).HasSchedule 3 ∧
      value (halveDesc d 2) ≤ (1 + Real.sqrt (value d)) / 2 ∧
      (value d = 1 → value (halveDesc d 2) = 1) :=
  halve_spec hd (by norm_num) (by norm_num) hsch

end Spec

end ShiQIP
