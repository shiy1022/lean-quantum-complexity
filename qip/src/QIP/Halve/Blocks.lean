import QIP.Halve.Embed
import QIP.Gen.Cut


namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

/-! ## Gate facts -/

theorem wires_lt_of_isSome {N : ℕ} {g : Gate} (hg : (g.toInstr? N).isSome) : ∀ w ∈ g.wires, w < N := by
  cases g <;> simp only [Gate.toInstr?, Gate.wires] at hg ⊢ <;> split_ifs at hg with h <;>
    simp_all

theorem isSome_mono {N N' : ℕ} (h : N ≤ N') {g : Gate} (hg : (g.toInstr? N).isSome) :
    (g.toInstr? N').isSome := by
  cases g <;> simp only [Gate.toInstr?] at hg ⊢ <;> split_ifs at hg ⊢ with h1 h2 <;> simp_all <;> omega

theorem relabel_id (g : Gate) : g.relabel id = g := by cases g <;> rfl

theorem notMem_support_of_filterMap {N : ℕ} {gs : List Gate} {c : Fin N} (hc : ∀ g ∈ gs, (c : ℕ) ∉ g.wires)
    {ι : Instr N} (hι : ι ∈ gs.filterMap (Gate.toInstr? N)) : c ∉ ι.support := by
  obtain ⟨g, hg, hgι⟩ := List.mem_filterMap.mp hι
  rw [mem_support_of_toInstr? hgι]
  exact hc g hg

variable {d : Desc} {n : ℕ}

/-- Gates of the halved description that avoid the coin and the control ancilla. -/
def Avoid (d : Desc) (n : ℕ) (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.toInstr? (halveDesc d n).totalWires).isSome ∧ hCoin d ∉ g.wires ∧ hCa d ∉ g.wires

theorem Avoid.append {gs gs' : List Gate} (h : Avoid d n gs) (h' : Avoid d n gs') : Avoid d n (gs ++ gs') := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · exact h' g hg

theorem avoid_nil : Avoid d n [] := fun _ h => absurd h List.not_mem_nil

theorem avoid_of_d {gs : List Gate} (hgs : ∀ g ∈ gs, (g.toInstr? d.totalWires).isSome) : Avoid d n gs := by
  intro g hg
  have hW := W_lt_total d n
  have hw := wires_lt_of_isSome (hgs g hg)
  refine ⟨isSome_mono (by omega) (hgs g hg), fun h => ?_, fun h => ?_⟩
  · have := hw _ h; unfold hCoin at this; omega
  · have := hw _ h; unfold hCa at this; omega

theorem avoid_swapRange {p q r : ℕ} (hq : q + r ≤ d.totalWires) (hp : hPriv d ≤ p)
    (hpr : p + r ≤ (halveDesc d n).totalWires) : Avoid d n (swapRange p q r) := by
  intro g hg
  simp only [swapRange, List.mem_flatMap, List.mem_range] at hg
  obtain ⟨i, hi, hg⟩ := hg
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp only [Gate.toInstr?, Gate.wires, hCoin, hCa, List.mem_cons, List.not_mem_nil, or_false] <;>
    refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> simp_all <;> omega


/-! ## Translated block lists -/

/-- The instructions of block `j` of `d`. -/
noncomputable def dI (d : Desc) (j : ℕ) : List (Instr d.totalWires) :=
  (d.blocks.getD j []).filterMap (Gate.toInstr? d.totalWires)

theorem filterMap_dBlock (hd : d.Valid) (j : ℕ) :
    (d.blocks.getD j []).filterMap (Gate.toInstr? (halveDesc d n).totalWires) =
      (dI d j).map (instrMap (workEmb d n)) := by
  have h := filterMap_relabel (workEmb d n) id (fun _ => rfl) _ (hd.toInstr?_isSome j)
  rw [show (d.blocks.getD j []).map (Gate.relabel id) = d.blocks.getD j [] by
    conv_rhs => rw [← List.map_id (d.blocks.getD j [])]
    exact List.map_congr_left fun g _ => relabel_id g] at h
  exact h

theorem instrInv_map {N M : ℕ} (f : Fin N ↪ Fin M) (g : Instr N) :
    instrInv (instrMap f g) = (instrInv g).map (instrMap f) := by
  cases g <;> simp [instrInv, instrMap, List.replicate]

theorem adjointInstrs_map {N M : ℕ} (f : Fin N ↪ Fin M) (l : List (Instr N)) :
    adjointInstrs (l.map (instrMap f)) = (adjointInstrs l).map (instrMap f) := by
  simp only [adjointInstrs, List.map_reverse, List.map_map, List.map_flatten]
  congr 1
  rw [← List.map_reverse, ← List.map_reverse]
  exact List.map_congr_left fun g _ => by simp [instrInv_map]

theorem filterMap_adjDBlock (hd : d.Valid) (j : ℕ) :
    (adjointGates (d.blocks.getD j [])).filterMap (Gate.toInstr? (halveDesc d n).totalWires) =
      (adjointInstrs (dI d j)).map (instrMap (workEmb d n)) := by
  rw [filterMap_adjointGates _ fun g hg => isSome_mono (by have := W_lt_total d n; omega)
    (hd.toInstr?_isSome j g hg), filterMap_dBlock hd, adjointInstrs_map]

/-! ## Blocks in the `d`-picture -/

variable {N₀ : Type} [Fintype N₀] [DecidableEq N₀]

theorem runLayer_dBlock (hd : d.Valid) (j : ℕ) (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ)
    (μ : N₀) :
    runLayer ((d.blocks.getD j []).filterMap (Gate.toInstr? (halveDesc d n).totalWires))
      (fun y => Φ b v (y, μ)) = fun y => Φ b (blockOp d (N₀ × MB d n) j *ᵥ v) (y, μ) := by
  rw [filterMap_dBlock hd, runLayer_work]
  rfl

theorem runLayer_adjDBlock (hd : d.Valid) (j : ℕ) (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ)
    (μ : N₀) :
    runLayer ((adjointGates (d.blocks.getD j [])).filterMap (Gate.toInstr? (halveDesc d n).totalWires))
      (fun y => Φ b v (y, μ)) = fun y => Φ b ((blockOp d (N₀ × MB d n) j)ᴴ *ᵥ v) (y, μ) := by
  rw [filterMap_adjDBlock hd, runLayer_work, layerMat_adjointInstrs, blockOp, conjTranspose_kronecker,
    conjTranspose_one]
  rfl

theorem hPay_ge (k : ℕ) : hPriv d ≤ hPay d n k := by
  unfold hPay; have := hPriv_le_hOff d n k; omega

theorem hPay_add_le {k j : ℕ} (_hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k) :
    hPay d n k + wd d j ≤ (halveDesc d n).totalWires := by
  rw [totalWires_halveDesc]
  have h1 := hOff_mono d n (show k + 1 ≤ n + 1 by omega)
  rw [hOff_succ] at h1
  unfold hPay
  split_ifs at h1 ⊢ <;> omega

omit [Fintype N₀] [DecidableEq N₀] in
theorem runLayer_swapMsg {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k) (b : Bool)
    (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer ((swapMsg d n k j).filterMap (Gate.toInstr? (halveDesc d n).totalWires))
      (fun y => Φ b v (y, μ)) =
        fun y => Φ b (v ∘ σSw d n (hPay d n k) (d.msgOffset j) (wd d j)) (y, μ) := by
  have h1 := msgOffset_add_width_le d j
  have h2 := hPay_ge (d := d) (n := n) k
  have h3 := hPay_add_le hk1 hkn hj
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  rw [show swapMsg d n k j = swapRange (hPay d n k) (d.msgOffset j) (wd d j) from rfl,
    runLayer_swapRange _ _ _ (by unfold wd at *; omega) h3]
  funext y
  exact Φ_swR (by unfold wd; omega) h2 h3 b v y μ

theorem avoid_swapMsg {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k) :
    Avoid d n (swapMsg d n k j) :=
  avoid_swapRange (by have := msgOffset_add_width_le d j; unfold wd; omega) (hPay_ge k)
    (hPay_add_le hk1 hkn hj)

/-! ## Controlled steps in the `d`-picture -/

omit [Fintype N₀] [DecidableEq N₀] in
theorem Φ_coin_ne {b : Bool} {v : Qubits d.totalWires × (N₀ × MB d n) → ℂ}
    {y : Qubits (halveDesc d n).totalWires} (hy : y (coinW d n) ≠ b) (μ : N₀) : Φ b v (y, μ) = 0 := by
  simp only [Φ]; rw [if_neg (fun h => hy h.1)]

omit [Fintype N₀] [DecidableEq N₀] in
theorem clean_Φ (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    Clean (caW d n) (fun y => Φ b v (y, μ)) := by
  intro z hz; simp only [Φ]; rw [if_neg (fun h => by rw [h.2.2.1] at hz; exact Bool.false_ne_true hz)]

theorem coinW_ne_caW : coinW d n ≠ caW d n := fun h => by
  have := congrArg Fin.val h; rw [coinW_val, caW_val] at this; omega

theorem filterMap_onF {gs : List Gate} (hA : Avoid d n gs) :
    (onF d gs).filterMap (Gate.toInstr? (halveDesc d n).totalWires) =
      [Instr.x (coinW d n)] ++ ctrlInstrs (coinW d n) (caW d n)
        (gs.filterMap (Gate.toInstr? (halveDesc d n).totalWires)) ++ [Instr.x (coinW d n)] := by
  have hc : hCoin d < (halveDesc d n).totalWires := (coinW d n).2
  rw [onF, List.filterMap_append, List.filterMap_append,
    show ctrlGates (hCoin d) (hCa d) gs = ctrlGates (coinW d n : ℕ) (caW d n : ℕ) gs from rfl,
    filterMap_ctrlGates (coinW d n) (caW d n) coinW_ne_caW gs hA]
  simp [Gate.toInstr?, hc]
  rfl

theorem filterMap_onB {gs : List Gate} (hA : Avoid d n gs) :
    (onB d gs).filterMap (Gate.toInstr? (halveDesc d n).totalWires) =
      ctrlInstrs (coinW d n) (caW d n) (gs.filterMap (Gate.toInstr? (halveDesc d n).totalWires)) :=
  filterMap_ctrlGates (coinW d n) (caW d n) coinW_ne_caW gs hA

theorem supp_of_avoid {gs : List Gate} (hA : Avoid d n gs) :
    ∀ g ∈ gs.filterMap (Gate.toInstr? (halveDesc d n).totalWires),
      coinW d n ∉ g.support ∧ caW d n ∉ g.support :=
  fun _ hg => ⟨notMem_support_of_filterMap (fun g hg' => (hA g hg').2.1) hg,
    notMem_support_of_filterMap (fun g hg' => (hA g hg').2.2) hg⟩

/-- A `d`-picture operation. -/
abbrev DOp (d : Desc) (n : ℕ) (N₀ : Type) : Type :=
  (Qubits d.totalWires × (N₀ × MB d n) → ℂ) → Qubits d.totalWires × (N₀ × MB d n) → ℂ

/-- A gate list acts as the `d`-picture operation `op`, for both coin values. -/
def Acts (gs : List Gate) (op : DOp d n N₀) : Prop :=
  ∀ b v μ, runLayer (gs.filterMap (Gate.toInstr? (halveDesc d n).totalWires)) (fun y => Φ b v (y, μ)) =
    fun y => Φ b (op v) (y, μ)

omit [Fintype N₀] [DecidableEq N₀] in
theorem Acts.append {gs gs' : List Gate} {op op' : DOp d n N₀} (h : Acts gs op) (h' : Acts gs' op') :
    Acts (gs ++ gs') (fun v => op' (op v)) := by
  intro b v μ
  rw [List.filterMap_append, runLayer_append, h, h']

omit [Fintype N₀] [DecidableEq N₀] in
theorem acts_nil : Acts (d := d) (n := n) (N₀ := N₀) [] id := fun _ _ _ => rfl

omit [Fintype N₀] [DecidableEq N₀] in
/-- **Controlled on the coin being `0`, in the `d`-picture.** -/
theorem runLayer_onF_Φ {gs : List Gate} (hA : Avoid d n gs) {op : DOp d n N₀} (hop : Acts gs op)
    (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer ((onF d gs).filterMap (Gate.toInstr? (halveDesc d n).totalWires)) (fun y => Φ b v (y, μ)) =
      fun y => Φ b (if b then v else op v) (y, μ) := by
  funext y
  rw [filterMap_onF hA, runLayer_onF coinW_ne_caW _ (supp_of_avoid hA) (clean_Φ b v μ), hop]
  cases b <;> cases hy : y (coinW d n) <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
    first
    | rfl
    | rw [Φ_coin_ne (y := y) (by rw [hy]; decide), Φ_coin_ne (y := y) (by rw [hy]; decide)]

omit [Fintype N₀] [DecidableEq N₀] in
/-- **Controlled on the coin being `1`, in the `d`-picture.** -/
theorem runLayer_onB_Φ {gs : List Gate} (hA : Avoid d n gs) {op : DOp d n N₀} (hop : Acts gs op)
    (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer ((onB d gs).filterMap (Gate.toInstr? (halveDesc d n).totalWires)) (fun y => Φ b v (y, μ)) =
      fun y => Φ b (if b then op v else v) (y, μ) := by
  funext y
  rw [filterMap_onB hA, runLayer_ctrlInstrs coinW_ne_caW _ (supp_of_avoid hA) (clean_Φ b v μ), hop]
  cases b <;> cases hy : y (coinW d n) <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
    first
    | rfl
    | rw [Φ_coin_ne (y := y) (by rw [hy]; decide), Φ_coin_ne (y := y) (by rw [hy]; decide)]

end ShiQIP
