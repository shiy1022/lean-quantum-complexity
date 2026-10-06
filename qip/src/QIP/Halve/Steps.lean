import QIP.Halve.Blocks
import QIP.Gen.Local


/-!
# Q31 — the blocks of the halved description in the `d`-picture

For `2 ≤ k ≤ n`, block `k'` acts on `Φ b v` as the forward step `fwdOp k` (coin `0`) or the
backward step `bwdOp k` (coin `1`), built from the swaps `swOp`, the blocks `bOp` of `d` and
their inverses `bOpH`.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

variable {d : Desc} {n : ℕ} {N₀ : Type} [Fintype N₀] [DecidableEq N₀]

variable (d n N₀) in
omit [Fintype N₀] [DecidableEq N₀] in
omit [Fintype N₀] [DecidableEq N₀] in
omit [Fintype N₀] [DecidableEq N₀] in
omit [Fintype N₀] [DecidableEq N₀] in
/-- Swap message `k'` with register `j` of `d`. -/
def swOp (k j : ℕ) : DOp d n N₀ := fun v => v ∘ σSw d n (hPay d n k) (d.msgOffset j) (wd d j)

variable (d n N₀) in
/-- Block `j` of `d`. -/
noncomputable def bOp (j : ℕ) : DOp d n N₀ := fun v => blockOp d (N₀ × MB d n) j *ᵥ v

variable (d n N₀) in
/-- The inverse of block `j` of `d`. -/
noncomputable def bOpH (j : ℕ) : DOp d n N₀ := fun v => (blockOp d (N₀ × MB d n) j)ᴴ *ᵥ v

/-- An operation applied when `c` holds. -/
def ifOp (c : Prop) [Decidable c] (op : DOp d n N₀) : DOp d n N₀ := if c then op else id

variable (d n N₀) in
/-- The forward step of block `k'`. -/
noncomputable def fwdOp (k : ℕ) : DOp d n N₀ := fun v =>
  ifOp (k % 2 = 1) (swOp d n N₀ k (n + k))
    (bOp d n N₀ (n + k) (ifOp ((k - 1) % 2 = 0) (swOp d n N₀ (k - 1) (n + k - 1)) v))

variable (d n N₀) in
/-- The backward step of block `k'`. -/
noncomputable def bwdOp (k : ℕ) : DOp d n N₀ := fun v =>
  ifOp (k % 2 = 1) (swOp d n N₀ k (n + 1 - k))
    (bOpH d n N₀ (n + 2 - k) (ifOp ((k - 1) % 2 = 0) (swOp d n N₀ (k - 1) (n + 2 - k)) v))

theorem wd_le_hw_fwd {k : ℕ} (hk : 1 ≤ k) : wd d (n + k) ≤ hw d n k := by
  unfold hw; rw [if_neg (by omega)]; exact le_max_left _ _

theorem wd_le_hw_bwd {k : ℕ} (hk : 1 ≤ k) : wd d (n + 1 - k) ≤ hw d n k := by
  unfold hw; rw [if_neg (by omega)]; exact le_max_right _ _

omit [Fintype N₀] [DecidableEq N₀] in
theorem acts_avoid_swap {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k) (c : Prop)
    [Decidable c] :
    Avoid d n (if c then swapMsg d n k j else []) ∧
      Acts (N₀ := N₀) (if c then swapMsg d n k j else []) (ifOp c (swOp d n N₀ k j)) := by
  by_cases hc : c
  · simp only [if_pos hc, ifOp]
    exact ⟨avoid_swapMsg hk1 hkn hj, fun b v μ => runLayer_swapMsg hk1 hkn hj b v μ⟩
  · simp only [if_neg hc, ifOp]
    exact ⟨avoid_nil, acts_nil⟩

theorem acts_avoid_dBlock (hd : d.Valid) (j : ℕ) :
    Avoid d n (d.blocks.getD j []) ∧ Acts (N₀ := N₀) (d.blocks.getD j []) (bOp d n N₀ j) :=
  ⟨avoid_of_d (hd.toInstr?_isSome j), fun b v μ => runLayer_dBlock hd j b v μ⟩

theorem acts_avoid_adjDBlock (hd : d.Valid) (j : ℕ) :
    Avoid d n (adjointGates (d.blocks.getD j [])) ∧
      Acts (N₀ := N₀) (adjointGates (d.blocks.getD j [])) (bOpH d n N₀ j) := by
  refine ⟨?_, fun b v μ => runLayer_adjDBlock hd j b v μ⟩
  have h := avoid_of_d (n := n) (hd.toInstr?_isSome j)
  intro g hg
  have hW := W_lt_total d n
  have hsome : ∀ g ∈ d.blocks.getD j [], (g.toInstr? (halveDesc d n).totalWires).isSome :=
    fun g hg => (h g hg).1
  have hmem := List.mem_flatten.mp hg
  obtain ⟨l, hl, hgl⟩ := hmem
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hl
  have h0 := h g₀ (List.mem_reverse.mp hg₀)
  cases g₀ <;> simp only [Gate.inv, List.mem_cons, List.not_mem_nil, or_false, List.mem_replicate,
    or_self] at hgl
  all_goals first
    | (subst hgl; exact h0)
    | (obtain ⟨_, hgl⟩ := hgl; subst hgl; exact h0)

theorem acts_avoid_fwdStep (hd : d.Valid) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    Avoid d n (fwdStep d n k) ∧ Acts (N₀ := N₀) (fwdStep d n k) (fwdOp d n N₀ k) := by
  have h1 := acts_avoid_swap (N₀ := N₀) (d := d) (show 1 ≤ k - 1 by omega) (show k - 1 ≤ n by omega)
    (show wd d (n + k - 1) ≤ hw d n (k - 1) by
      rw [show n + k - 1 = n + (k - 1) by omega]; exact wd_le_hw_fwd (by omega)) ((k - 1) % 2 = 0)
  have h2 := acts_avoid_dBlock (n := n) (N₀ := N₀) hd (n + k)
  have h3 := acts_avoid_swap (N₀ := N₀) (d := d) (show 1 ≤ k by omega) hkn
    (wd_le_hw_fwd (by omega)) (k % 2 = 1)
  exact ⟨(h1.1.append h2.1).append h3.1, (h1.2.append h2.2).append h3.2⟩

theorem acts_avoid_bwdStep (hd : d.Valid) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    Avoid d n (bwdStep d n k) ∧ Acts (N₀ := N₀) (bwdStep d n k) (bwdOp d n N₀ k) := by
  have h1 := acts_avoid_swap (N₀ := N₀) (d := d) (show 1 ≤ k - 1 by omega) (show k - 1 ≤ n by omega)
    (show wd d (n + 2 - k) ≤ hw d n (k - 1) by
      rw [show n + 2 - k = n + 1 - (k - 1) by omega]; exact wd_le_hw_bwd (by omega)) ((k - 1) % 2 = 0)
  have h2 := acts_avoid_adjDBlock (n := n) (N₀ := N₀) hd (n + 2 - k)
  have h3 := acts_avoid_swap (N₀ := N₀) (d := d) (show 1 ≤ k by omega) hkn
    (wd_le_hw_bwd (by omega)) (k % 2 = 1)
  exact ⟨(h1.1.append h2.1).append h3.1, (h1.2.append h2.2).append h3.2⟩

/-- **A middle block in the `d`-picture.** -/
theorem runLayer_hBlock_mid (hd : d.Valid) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) (b : Bool)
    (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer ((hBlock d n k).filterMap (Gate.toInstr? (halveDesc d n).totalWires)) (fun y => Φ b v (y, μ)) =
      fun y => Φ b (if b then bwdOp d n N₀ k v else fwdOp d n N₀ k v) (y, μ) := by
  have hF := acts_avoid_fwdStep (N₀ := N₀) hd hk2 hkn
  have hB := acts_avoid_bwdStep (N₀ := N₀) hd hk2 hkn
  rw [hBlock, if_neg (by omega), if_neg (by omega), if_pos hkn, List.filterMap_append, runLayer_append,
    runLayer_onF_Φ hF.1 hF.2, runLayer_onB_Φ hB.1 hB.2]
  cases b <;> rfl

/-! ## Blocks as matrices -/

theorem blocks_getD_halve {k : ℕ} (hk : k ≤ n + 1) : (halveDesc d n).blocks.getD k [] = hBlock d n k := by
  simp [halveDesc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : k < n + 2)]

theorem kron_layer_mulVec {M : ℕ} (l : List (Instr M)) (ψ : Qubits M × N₀ → ℂ) :
    (layerMat l ⊗ₖ (1 : Matrix N₀ N₀ ℂ)) *ᵥ ψ = fun p => runLayer l (fun y => ψ (y, p.2)) p.1 := by
  funext ⟨y, μ⟩
  rw [kronOne_mulVec_apply, layerMat_mulVec]

/-- A block of the halved description, as a matrix, from its action on slices. -/
theorem blockMat_halve_Φ {k : ℕ} (hk : k ≤ n + 1) (b : Bool) (v w : Qubits d.totalWires × (N₀ × MB d n) → ℂ)
    (h : ∀ μ, runLayer ((hBlock d n k).filterMap (Gate.toInstr? (halveDesc d n).totalWires))
      (fun y => Φ b v (y, μ)) = fun y => Φ b w (y, μ)) :
    (blockMat (halveDesc d n) k ⊗ₖ (1 : Matrix N₀ N₀ ℂ)) *ᵥ Φ b v = Φ b w := by
  rw [blockMat, blocks_getD_halve hk, kron_layer_mulVec]
  funext ⟨y, μ⟩
  exact congrFun (h μ) y


/-! ## Linearity -/

theorem runLayer_add {M : ℕ} (l : List (Instr M)) (ψ ψ' : QState M) :
    runLayer l (ψ + ψ') = runLayer l ψ + runLayer l ψ' := by
  rw [← layerMat_mulVec, ← layerMat_mulVec, ← layerMat_mulVec, mulVec_add]

theorem runLayer_smul {M : ℕ} (l : List (Instr M)) (c : ℂ) (ψ : QState M) :
    runLayer l (c • ψ) = c • runLayer l ψ := by
  rw [← layerMat_mulVec, ← layerMat_mulVec, mulVec_smul]

/-! ## The cut state -/

theorem inReg_zero_iff (w : Fin (halveDesc d n).totalWires) :
    inReg (halveDesc d n) 0 w ↔ hPriv d ≤ (w : ℕ) ∧ (w : ℕ) < hPriv d + d.totalWires := by
  unfold inReg
  rw [msgOffset_halveDesc d n 0 (by omega), width_hMsgs d n 0 (by omega)]
  simp [hOff, hw]

variable (d n) in
/-- A working-copy label as a label of message `0'`. -/
def regOf (x : Qubits d.totalWires) : Reg (halveDesc d n) 0 :=
  fun w => x ⟨w.1 - hPriv d, by have := (inReg_zero_iff w.1).mp w.2; omega⟩

variable (d n) in
/-- The prover's first message, applied to `|0⟩` and the initial memory. -/
noncomputable def cvec (A : Matrix (Reg (halveDesc d n) 0 × N₀) (Reg (halveDesc d n) 0 × N₀) ℂ)
    (ι : N₀ → ℂ) (p : Reg (halveDesc d n) 0 × N₀) : ℂ :=
  ∑ μ, A p ((fun _ => false), μ) * ι μ

variable (d n) in
/-- **The cut state** in the `d`-picture: the working copy carries message `0'`, all message
wires are `0`. -/
noncomputable def cutVec (A : Matrix (Reg (halveDesc d n) 0 × N₀) (Reg (halveDesc d n) 0 × N₀) ℂ)
    (ι : N₀ → ℂ) : Qubits d.totalWires × (N₀ × MB d n) → ℂ :=
  fun z => if ∀ u, z.2.2 u = false then cvec d n A ι (regOf d n z.1, z.2.1) else 0

omit [DecidableEq N₀] in
theorem tv_zero (A : Matrix (Reg (halveDesc d n) 0 × N₀) (Reg (halveDesc d n) 0 × N₀) ℂ) (ι : N₀ → ℂ)
    (y : Qubits (halveDesc d n).totalWires) (μ' : N₀) :
    tv 0 A (fun p => zeroVec (halveDesc d n).totalWires p.1 * ι p.2) (y, μ') =
      if ∀ w, ¬ inReg (halveDesc d n) 0 w → y w = false then
        cvec d n A ι ((wireSplitE (halveDesc d n) 0 y).2, μ') else 0 := by
  rw [tv_apply]
  have hz : ∀ x : Reg (halveDesc d n) 0, zeroVec (halveDesc d n).totalWires
      (PrefixData.regSet (halveDesc d n) 0 y x) =
        if (∀ w, ¬ inReg (halveDesc d n) 0 w → y w = false) ∧ x = (fun _ => false) then 1 else 0 := by
    intro x
    simp only [zeroVec]
    congr 1
    apply propext
    constructor
    · intro h
      refine ⟨fun w hw => ?_, funext fun w => ?_⟩
      · have := congrFun h w; rwa [PrefixData.regSet_apply, dif_neg hw] at this
      · have := congrFun h w.1; rwa [PrefixData.regSet_apply, dif_pos w.2] at this
    · rintro ⟨h1, rfl⟩
      funext w
      rw [PrefixData.regSet_apply]
      split_ifs with hw
      · rfl
      · exact h1 w hw
  simp only [hz, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  by_cases h : ∀ w, ¬ inReg (halveDesc d n) 0 w → y w = false
  · simp only [and_iff_right h, if_pos h]
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp only [if_true]; rfl
    · intro x _ hx; simp [hx]
    · simp
  · simp only [h, false_and, if_false, Finset.sum_const_zero]

/-- The swap of message `0'` into the working copy. -/
def swap0 (d : Desc) (n : ℕ) : List Gate :=
  (List.range d.totalWires).flatMap fun x => swapGates (hOff d n 0 + x) x

theorem swap0_eq : swap0 d n = swapRange (hPriv d) 0 d.totalWires := by
  simp [swap0, swapRange, hOff]

theorem hPriv_add_W_le : hPriv d + d.totalWires ≤ (halveDesc d n).totalWires := by
  rw [totalWires_halveDesc]
  have h1 := hOff_mono d n (show 1 ≤ n + 1 by omega)
  have h2 : hOff d n 1 = hPriv d + d.totalWires := by rw [hOff_succ]; simp [hOff, hw]
  omega

omit [DecidableEq N₀] in
theorem Φ_false_cut (A : Matrix (Reg (halveDesc d n) 0 × N₀) (Reg (halveDesc d n) 0 × N₀) ℂ)
    (ι : N₀ → ℂ) (y : Qubits (halveDesc d n).totalWires) (μ : N₀) :
    Φ false (cutVec d n A ι) (y, μ) = if ∀ w : Fin (halveDesc d n).totalWires, d.totalWires ≤ (w : ℕ) →
      y w = false then cvec d n A ι (regOf d n (workPart y), μ) else 0 := by
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  simp only [Φ, cutVec]
  by_cases h : ∀ w : Fin (halveDesc d n).totalWires, d.totalWires ≤ (w : ℕ) → y w = false
  · rw [if_pos h, if_pos, if_pos]
    · intro u; exact h u.1 (by have := u.2; omega)
    · refine ⟨h _ (by rw [coinW_val]), h _ (by rw [outW_val]; omega), h _ (by rw [caW_val]; omega),
        fun w h1 _ => h w (by omega)⟩
  · rw [if_neg h]
    push Not at h
    obtain ⟨w, hw, hyw⟩ := h
    replace hyw : y w = true := by simpa using hyw
    split_ifs with h1 h2
    · exfalso
      by_cases e1 : (w : ℕ) < hPriv d
      · by_cases e2 : (w : ℕ) = d.totalWires
        · have : w = coinW d n := Fin.ext e2
          rw [this, h1.1] at hyw; exact Bool.false_ne_true hyw
        by_cases e3 : (w : ℕ) = d.totalWires + 1
        · have : w = outW d n := Fin.ext e3
          rw [this, h1.2.1] at hyw; exact Bool.false_ne_true hyw
        by_cases e4 : (w : ℕ) = d.totalWires + 2
        · have : w = caW d n := Fin.ext e4
          rw [this, h1.2.2.1] at hyw; exact Bool.false_ne_true hyw
        rw [h1.2.2.2 w (by omega) e1] at hyw; exact Bool.false_ne_true hyw
      · have := h2 ⟨w, by omega⟩
        simp only [msgPart] at this
        rw [this] at hyw; exact Bool.false_ne_true hyw
    · rfl
    · rfl


omit [DecidableEq N₀] in
theorem runLayer_swap0 (A : Matrix (Reg (halveDesc d n) 0 × N₀) (Reg (halveDesc d n) 0 × N₀) ℂ) (ι : N₀ → ℂ)
    (μ : N₀) :
    runLayer ((swap0 d n).filterMap (Gate.toInstr? (halveDesc d n).totalWires))
      (fun y => tv 0 A (fun p => zeroVec (halveDesc d n).totalWires p.1 * ι p.2) (y, μ)) =
        fun y => Φ false (cutVec d n A ι) (y, μ) := by
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have hle := hPriv_add_W_le (d := d) (n := n)
  rw [swap0_eq, runLayer_swapRange _ _ _ (by omega) hle]
  funext y
  rw [tv_zero, Φ_false_cut]
  have hsw : ∀ w : Fin (halveDesc d n).totalWires, (swR (hPriv d) 0 d.totalWires w : ℕ) =
      if hPriv d ≤ (w : ℕ) ∧ (w : ℕ) < hPriv d + d.totalWires then (w : ℕ) - hPriv d
      else if (w : ℕ) < d.totalWires then hPriv d + w else w := by
    intro w; rw [val_swR]; split_ifs <;> omega
  have hcond : (∀ w, ¬ inReg (halveDesc d n) 0 w → (y ∘ swR (hPriv d) 0 d.totalWires) w = false) ↔
      ∀ w : Fin (halveDesc d n).totalWires, d.totalWires ≤ (w : ℕ) → y w = false := by
    constructor
    · intro h w hw
      by_cases hr : hPriv d ≤ (w : ℕ) ∧ (w : ℕ) < hPriv d + d.totalWires
      · have := h ⟨w - hPriv d, by omega⟩ (by rw [inReg_zero_iff]; simp only; omega)
        simp only [Function.comp_apply] at this
        rwa [show swR (hPriv d) 0 d.totalWires ⟨w - hPriv d, by omega⟩ = w from
          Fin.ext (by rw [hsw]; simp only; split_ifs <;> omega)] at this
      · have := h w (by rw [inReg_zero_iff]; exact hr)
        simp only [Function.comp_apply] at this
        rwa [show swR (hPriv d) 0 d.totalWires w = w from Fin.ext (by rw [hsw]; split_ifs <;> omega)]
          at this
    · intro h w hw
      rw [inReg_zero_iff] at hw
      exact h _ (by rw [hsw]; split_ifs <;> omega)
  rw [if_congr hcond rfl rfl]
  split_ifs with h
  · congr 2
    funext w
    have hw := (inReg_zero_iff w.1).mp w.2
    simp only [regOf, workPart, wireSplitE, Equiv.trans_apply, Equiv.piEquivPiSubtypeProd_apply,
      Equiv.prodComm_apply, Prod.snd_swap, Function.comp_apply]
    congr 1
    apply Fin.ext
    rw [hsw]
    simp only [workEmb, Fin.castLEEmb_apply, Fin.val_castLE]
    split_ifs
    omega
  · rfl

theorem update_coin_ctlOK (b : Bool) (y : Qubits (halveDesc d n).totalWires) :
    ctlOK b (Function.update y (coinW d n) b) ↔ ctlOK (y (coinW d n)) y := by
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  unfold ctlOK
  have hne : ∀ w : Fin (halveDesc d n).totalWires, (w : ℕ) ≠ d.totalWires → w ≠ coinW d n :=
    fun w h e => h (by rw [e]; rfl)
  rw [Function.update_self, Function.update_of_ne (hne _ (by rw [outW_val]; omega)),
    Function.update_of_ne (hne _ (by rw [caW_val]; omega))]
  simp only [true_and]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun w => forall_congr' fun h1 =>
    forall_congr' fun _ => ?_))
  rw [Function.update_of_ne (hne w (by omega))]

theorem workPart_update_coin (b : Bool) (y : Qubits (halveDesc d n).totalWires) :
    workPart (Function.update y (coinW d n) b) = workPart y := by
  funext x
  simp only [workPart]
  rw [Function.update_of_ne]
  intro e
  have := congrArg Fin.val e
  simp [workEmb, coinW_val] at this
  omega

theorem msgPart_update_coin (b : Bool) (y : Qubits (halveDesc d n).totalWires) :
    msgPart (Function.update y (coinW d n) b) = msgPart y := by
  funext u
  simp only [msgPart]
  rw [Function.update_of_ne]
  intro e
  have := congrArg Fin.val e
  have := u.2
  rw [coinW_val] at *
  unfold hPriv at *
  omega

omit [Fintype N₀] [DecidableEq N₀] in
theorem Φ_update_coin (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (b : Bool)
    (y : Qubits (halveDesc d n).totalWires) (μ : N₀) :
    Φ b v (Function.update y (coinW d n) b, μ) = Φ (y (coinW d n)) v (y, μ) := by
  simp only [Φ, workPart_update_coin, msgPart_update_coin]
  exact if_congr (update_coin_ctlOK b y) rfl rfl

omit [Fintype N₀] [DecidableEq N₀] in
theorem Φ_split (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (y : Qubits (halveDesc d n).totalWires)
    (μ : N₀) : Φ (y (coinW d n)) v (y, μ) = Φ false v (y, μ) + Φ true v (y, μ) := by
  cases h : y (coinW d n)
  · rw [Φ_coin_ne (b := true) (by rw [h]; decide), add_zero]
  · rw [Φ_coin_ne (b := false) (by rw [h]; decide), zero_add]

omit [Fintype N₀] [DecidableEq N₀] in
/-- **The coin's Hadamard.** -/
theorem runLayer_h_coin (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer [Instr.h (coinW d n)] (fun y => Φ false v (y, μ)) =
      (Real.sqrt 2 : ℂ)⁻¹ • fun y => Φ false v (y, μ) + Φ true v (y, μ) := by
  funext y
  rw [runLayer_cons, runLayer_nil, apply_h, Φ_update_coin, Φ_coin_ne (y := Function.update y (coinW d n) true)
    (by rw [Function.update_self]; decide), mul_zero, add_zero, Φ_split]
  simp only [hMat, of_apply, Bool.and_false, Bool.false_eq_true, if_false, Pi.smul_apply, smul_eq_mul]

theorem total_pos : 0 < (halveDesc d n).totalWires := by have := W_lt_total d n; omega

variable (d n) in
omit [Fintype N₀] [DecidableEq N₀] in
omit [Fintype N₀] [DecidableEq N₀] in
omit [Fintype N₀] [DecidableEq N₀] in
/-- The public copy of the coin, the first wire of message `1'` (for `n ≥ 1`). -/
def copyW : Fin (halveDesc d n).totalWires :=
  ⟨min (hOff d n 1) ((halveDesc d n).totalWires - 1), by have := total_pos (d := d) (n := n); omega⟩

theorem copyW_val (hn : 1 ≤ n) : ((copyW d n : Fin _) : ℕ) = hOff d n 1 := by
  have h1 := hOff_mono d n (show 2 ≤ n + 1 by omega)
  have h2 : hOff d n 2 = hOff d n 1 + (hw d n 1 + 1) := by simpa using hOff_succ d n 1
  have h3 := totalWires_halveDesc d n
  simp only [copyW]
  omega

theorem hPriv_le_copyW (hn : 1 ≤ n) : hPriv d ≤ ((copyW d n : Fin _) : ℕ) := by
  rw [copyW_val hn]; exact hPriv_le_hOff d n 1

variable (d n N₀) in
/-- Flip the coin copy in the `d`-picture. -/
def flipZ (z : Qubits d.totalWires × (N₀ × MB d n)) : Qubits d.totalWires × (N₀ × MB d n) :=
  (z.1, (z.2.1, fun u => if u.1 = copyW d n then !z.2.2 u else z.2.2 u))

omit [Fintype N₀] [DecidableEq N₀] in
theorem flipZ_flipZ (z : Qubits d.totalWires × (N₀ × MB d n)) : flipZ d n N₀ (flipZ d n N₀ z) = z := by
  obtain ⟨x, μ, β⟩ := z
  simp only [flipZ, Prod.mk.injEq, true_and]
  funext u
  split_ifs <;> simp

theorem coinW_ne_copyW : coinW d n ≠ copyW d n := fun h => by
  have := congrArg Fin.val h
  have h1 := hPriv_le_hOff d n 1
  have h2 := W_lt_total d n
  rw [coinW_val] at this; simp only [copyW] at this; unfold hPriv at h1; omega

omit [Fintype N₀] [DecidableEq N₀] in
/-- **The coin's public copy.** -/
theorem runLayer_cnot_copy (hn : 1 ≤ n) (v v' : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer [Instr.cnot (coinW d n) (copyW d n) coinW_ne_copyW]
      (fun y => Φ false v (y, μ) + Φ true v' (y, μ)) =
        fun y => Φ false v (y, μ) + Φ true (v' ∘ flipZ d n N₀) (y, μ) := by
  funext y
  rw [runLayer_cons, runLayer_nil, apply_cnot]
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have h2 := hPriv_le_copyW (d := d) hn
  have hne : ∀ w : Fin (halveDesc d n).totalWires, (w : ℕ) < hPriv d → w ≠ copyW d n :=
    fun w h e => by rw [e] at h; omega
  have hctl : ∀ b, ctlOK b (cnotFun (coinW d n) (copyW d n) y) ↔ ctlOK b y := by
    intro b
    unfold ctlOK
    simp only [cnotFun]
    rw [Function.update_of_ne (hne _ (by rw [coinW_val]; omega)),
      Function.update_of_ne (hne _ (by rw [outW_val]; omega)),
      Function.update_of_ne (hne _ (by rw [caW_val]; omega))]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun w =>
      forall_congr' fun h1 => forall_congr' fun h3 => ?_)))
    rw [Function.update_of_ne (hne w h3)]
  have hwork : workPart (cnotFun (coinW d n) (copyW d n) y) = workPart y := by
    funext x; simp only [workPart, cnotFun]
    rw [Function.update_of_ne (hne _ (by simp [workEmb]; omega))]
  have hmsg : msgPart (cnotFun (coinW d n) (copyW d n) y) =
      if y (coinW d n) then (flipZ d n N₀ (workPart y, (μ, msgPart y))).2.2 else msgPart y := by
    funext u
    simp only [msgPart, cnotFun, flipZ]
    by_cases h1 : u.1 = copyW d n <;> cases hc : y (coinW d n) <;> simp [h1, msgPart]
  simp only [Φ, hctl, hwork, hmsg]
  cases hc : y (coinW d n)
  · simp only [if_false, Bool.false_eq_true]
    congr 1
    split_ifs with h
    · exact absurd h.1 (by rw [hc]; decide)
    · rfl
  · simp only [if_true]
    congr 1
    · split_ifs with h
      · exact absurd h.1 (by rw [hc]; decide)
      · rfl


theorem filterMap_h_cnot (hn : 1 ≤ n) :
    [Gate.h (hCoin d), Gate.cnot (hCoin d) (hOff d n 1)].filterMap (Gate.toInstr? (halveDesc d n).totalWires) =
      [Instr.h (coinW d n), Instr.cnot (coinW d n) (copyW d n) coinW_ne_copyW] := by
  have h1 : hCoin d < (halveDesc d n).totalWires := (coinW d n).2
  have h2 : hOff d n 1 < (halveDesc d n).totalWires := by rw [← copyW_val hn]; exact (copyW d n).2
  have h3 : hCoin d ≠ hOff d n 1 := by
    have := hPriv_le_hOff d n 1; unfold hCoin; unfold hPriv at this; omega
  simp only [List.filterMap_cons, List.filterMap_nil, Gate.toInstr?, dif_pos h1,
    dif_pos (show hCoin d < _ ∧ hOff d n 1 < _ ∧ hCoin d ≠ hOff d n 1 from ⟨h1, h2, h3⟩)]
  congr 2
  simp only [Instr.cnot.injEq]
  exact ⟨rfl, Fin.ext (copyW_val (d := d) hn).symm⟩

/-- **Block `1'` in the `d`-picture**: the cut state enters the working copy, the coin is put in
superposition and copied into message `1'`, and both steps of the block run. -/
theorem runLayer_hBlock_one (hd : d.Valid) (hn : 1 ≤ n)
    (A : Matrix (Reg (halveDesc d n) 0 × N₀) (Reg (halveDesc d n) 0 × N₀) ℂ) (ι : N₀ → ℂ) (μ : N₀) :
    runLayer ((hBlock d n 1).filterMap (Gate.toInstr? (halveDesc d n).totalWires))
      (fun y => tv 0 A (fun p => zeroVec (halveDesc d n).totalWires p.1 * ι p.2) (y, μ)) =
        (Real.sqrt 2 : ℂ)⁻¹ • fun y => Φ false (swOp d n N₀ 1 (n + 1) (cutVec d n A ι)) (y, μ) +
          Φ true (swOp d n N₀ 1 n (bOpH d n N₀ (n + 1) (cutVec d n A ι ∘ flipZ d n N₀))) (y, μ) := by
  have hF : Avoid d n (swapMsg d n 1 (n + 1)) ∧ Acts (N₀ := N₀) (swapMsg d n 1 (n + 1)) (swOp d n N₀ 1 (n + 1)) :=
    ⟨avoid_swapMsg le_rfl hn (wd_le_hw_fwd le_rfl),
      fun b v μ => runLayer_swapMsg le_rfl hn (wd_le_hw_fwd le_rfl) b v μ⟩
  have hS : Avoid d n (swapMsg d n 1 n) ∧ Acts (N₀ := N₀) (swapMsg d n 1 n) (swOp d n N₀ 1 n) := by
    have hw : wd d n ≤ hw d n 1 := by simpa using wd_le_hw_bwd (d := d) (n := n) (k := 1) le_rfl
    exact ⟨avoid_swapMsg le_rfl hn hw, fun b v μ => runLayer_swapMsg le_rfl hn hw b v μ⟩
  have hB := acts_avoid_adjDBlock (n := n) (N₀ := N₀) hd (n + 1)
  have hB' := (hB.1.append hS.1)
  have hB'' := (hB.2.append hS.2)
  rw [hBlock, if_neg (by omega), if_pos rfl, List.filterMap_append, List.filterMap_append, List.filterMap_append,
    runLayer_append, runLayer_append, runLayer_append, ← swap0, runLayer_swap0, filterMap_h_cnot hn,
    show [Instr.h (coinW d n), Instr.cnot (coinW d n) (copyW d n) coinW_ne_copyW] =
      [Instr.h (coinW d n)] ++ [Instr.cnot (coinW d n) (copyW d n) coinW_ne_copyW] from rfl,
    runLayer_append, runLayer_h_coin, runLayer_smul, runLayer_cnot_copy hn, runLayer_smul, runLayer_smul,
    show (fun y => Φ false (cutVec d n A ι) (y, μ) + Φ true (cutVec d n A ι ∘ flipZ d n N₀) (y, μ)) =
      (fun y => Φ false (cutVec d n A ι) (y, μ)) + fun y => Φ true (cutVec d n A ι ∘ flipZ d n N₀) (y, μ)
      from rfl, runLayer_add, runLayer_add, runLayer_onF_Φ hF.1 hF.2, runLayer_onF_Φ hF.1 hF.2,
    runLayer_onB_Φ hB' hB'', runLayer_onB_Φ hB' hB'']
  rfl


/-! ## The final block -/

variable (d n) in
/-- The output wire of `d`, in the working copy. -/
def outD (hd : d.Valid) : Fin (halveDesc d n).totalWires := workEmb d n ⟨d.out, out_lt_W hd⟩

theorem outD_val (hd : d.Valid) : ((outD d n hd : Fin _) : ℕ) = d.out := rfl

theorem outD_ne_outW (hd : d.Valid) : outD d n hd ≠ outW d n := fun h => by
  have := congrArg Fin.val h
  rw [outD_val, outW_val] at this
  have := out_lt_W hd
  omega

/-- The forward gates of the final block, before the output copy. -/
def finF (d : Desc) (n : ℕ) : List Gate := swapMsg d n n (2 * n) ++ d.blocks.getD (2 * n + 1) []

/-- The backward gates of the final block. -/
def finB (d : Desc) (n : ℕ) : List Gate :=
  swapMsg d n n 1 ++ adjointGates (d.blocks.getD 1 []) ++ adjointGates (d.blocks.getD 0 [])

variable (d n N₀) in
/-- The forward step of the final block. -/
noncomputable def finFOp : DOp d n N₀ := fun v => bOp d n N₀ (2 * n + 1) (swOp d n N₀ n (2 * n) v)

variable (d n N₀) in
/-- The backward step of the final block. -/
noncomputable def finBOp : DOp d n N₀ := fun v => bOpH d n N₀ 0 (bOpH d n N₀ 1 (swOp d n N₀ n 1 v))

theorem acts_avoid_finF (hd : d.Valid) (hn : 1 ≤ n) :
    Avoid d n (finF d n) ∧ Acts (N₀ := N₀) (finF d n) (finFOp d n N₀) := by
  have hw : wd d (2 * n) ≤ hw d n n := by
    rw [show 2 * n = n + n by omega]; exact wd_le_hw_fwd hn
  have h1 : Avoid d n (swapMsg d n n (2 * n)) ∧ Acts (N₀ := N₀) (swapMsg d n n (2 * n)) (swOp d n N₀ n (2 * n)) :=
    ⟨avoid_swapMsg hn le_rfl hw, fun b v μ => runLayer_swapMsg hn le_rfl hw b v μ⟩
  have h2 := acts_avoid_dBlock (n := n) (N₀ := N₀) hd (2 * n + 1)
  exact ⟨h1.1.append h2.1, h1.2.append h2.2⟩

theorem acts_avoid_finB (hd : d.Valid) (hn : 1 ≤ n) :
    Avoid d n (finB d n) ∧ Acts (N₀ := N₀) (finB d n) (finBOp d n N₀) := by
  have hw : wd d 1 ≤ hw d n n := by
    have := wd_le_hw_bwd (d := d) (n := n) (k := n) hn; rwa [show n + 1 - n = 1 by omega] at this
  have h1 : Avoid d n (swapMsg d n n 1) ∧ Acts (N₀ := N₀) (swapMsg d n n 1) (swOp d n N₀ n 1) :=
    ⟨avoid_swapMsg hn le_rfl hw, fun b v μ => runLayer_swapMsg hn le_rfl hw b v μ⟩
  have h2 := acts_avoid_adjDBlock (n := n) (N₀ := N₀) hd 1
  have h3 := acts_avoid_adjDBlock (n := n) (N₀ := N₀) hd 0
  exact ⟨(h1.1.append h2.1).append h3.1, (h1.2.append h2.2).append h3.2⟩

theorem avoid_cnot_out (hd : d.Valid) : Avoid d n [Gate.cnot d.out (hOut d)] := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  have h1 := out_lt_W hd
  have h2 := W_lt_total d n
  refine ⟨?_, ?_, ?_⟩
  · rw [Gate.toInstr?_isSome_iff]
    simp only [Gate.okBool, hOut]
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨lt_of_lt_of_le h1 (by omega), decide_eq_true (by omega)⟩, by omega⟩
  · simp [Gate.wires, hCoin, hOut]; omega
  · simp [Gate.wires, hCa, hOut]; omega

theorem filterMap_cnot_out (hd : d.Valid) :
    [Gate.cnot d.out (hOut d)].filterMap (Gate.toInstr? (halveDesc d n).totalWires) =
      [Instr.cnot (outD d n hd) (outW d n) (outD_ne_outW hd)] := by
  have h1 := out_lt_W hd
  have h2 := W_lt_total d n
  have h3 : hOut d < (halveDesc d n).totalWires := (outW d n).2
  simp only [List.filterMap_cons, List.filterMap_nil, Gate.toInstr?]
  rw [dif_pos ⟨by omega, h3, by unfold hOut; omega⟩]
  rfl

/-- **The forward step of the final block**, with the copy of the output of `d`. -/
theorem runLayer_onF_fin (hd : d.Valid) (hn : 1 ≤ n) (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ)
    (μ : N₀) (y : Qubits (halveDesc d n).totalWires) :
    runLayer ((onF d (finF d n ++ [Gate.cnot d.out (hOut d)])).filterMap
      (Gate.toInstr? (halveDesc d n).totalWires)) (fun y => Φ b v (y, μ)) y =
        if b then Φ b v (y, μ) else Φ false (finFOp d n N₀ v) (cnotFun (outD d n hd) (outW d n) y, μ) := by
  have hF := acts_avoid_finF (N₀ := N₀) hd hn
  have hA := hF.1.append (avoid_cnot_out (n := n) hd)
  rw [filterMap_onF hA, runLayer_onF coinW_ne_caW _ (supp_of_avoid hA) (clean_Φ b v μ), List.filterMap_append,
    runLayer_append, hF.2, filterMap_cnot_out hd, runLayer_cons, runLayer_nil, apply_cnot]
  have hc : cnotFun (outD d n hd) (outW d n) y (coinW d n) = y (coinW d n) := by
    simp only [cnotFun]
    rw [Function.update_of_ne]
    intro e; have := congrArg Fin.val e; rw [coinW_val, outW_val] at this; omega
  cases b <;> cases hy : y (coinW d n) <;> simp only [if_true, if_false, Bool.false_eq_true]
  · exact (Φ_coin_ne (y := y) (by rw [hy]; decide) μ).trans
      (Φ_coin_ne (y := cnotFun (outD d n hd) (outW d n) y) (by rw [hc, hy]; decide) μ).symm
  · exact (Φ_coin_ne (y := cnotFun (outD d n hd) (outW d n) y) (by rw [hc, hy]; decide) μ).trans
      (Φ_coin_ne (y := y) (by rw [hy]; decide) μ).symm

theorem runLayer_zero {M : ℕ} (l : List (Instr M)) : runLayer l (0 : QState M) = 0 := by
  rw [← layerMat_mulVec, mulVec_zero]

/-- A circuit avoiding the coin keeps a state vanishing at coin value `b`. -/
theorem runLayer_vanish {l : List (Instr (halveDesc d n).totalWires)} (hl : ∀ g ∈ l, coinW d n ∉ g.support)
    {b : Bool} {ψ : QState (halveDesc d n).totalWires} (hψ : ∀ y, y (coinW d n) = b → ψ y = 0)
    (y : Qubits (halveDesc d n).totalWires) (hy : y (coinW d n) = b) : runLayer l ψ y = 0 := by
  have h := runLayer_sliceEq (w := coinW d n) (b := b) l hl (φ := ψ) (φ' := 0)
    (fun z hz => by rw [hψ z hz]; rfl)
  rw [h y hy, runLayer_zero]; rfl

/-- **The backward step of the final block.** -/
theorem runLayer_onB_fin (hd : d.Valid) (hn : 1 ≤ n) (F B : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer ((onB d (finB d n)).filterMap (Gate.toInstr? (halveDesc d n).totalWires))
      (fun y => Φ false F (cnotFun (outD d n hd) (outW d n) y, μ) + Φ true B (y, μ)) =
        fun y => Φ false F (cnotFun (outD d n hd) (outW d n) y, μ) + Φ true (finBOp d n N₀ B) (y, μ) := by
  have hB := acts_avoid_finB (N₀ := N₀) hd hn
  have hc : ∀ y : Qubits (halveDesc d n).totalWires,
      cnotFun (outD d n hd) (outW d n) y (coinW d n) = y (coinW d n) := by
    intro y
    simp only [cnotFun]
    rw [Function.update_of_ne]
    intro e; have := congrArg Fin.val e; rw [coinW_val, outW_val] at this; omega
  have hca : ∀ y : Qubits (halveDesc d n).totalWires,
      cnotFun (outD d n hd) (outW d n) y (caW d n) = y (caW d n) := by
    intro y
    simp only [cnotFun]
    rw [Function.update_of_ne]
    intro e; have := congrArg Fin.val e; rw [caW_val, outW_val] at this; omega
  have hclean : Clean (caW d n) (fun y => Φ false F (cnotFun (outD d n hd) (outW d n) y, μ) + Φ true B (y, μ)) := by
    intro z hz
    have e1 := clean_Φ false F μ (cnotFun (outD d n hd) (outW d n) z) (by rw [hca]; exact hz)
    have e2 := clean_Φ true B μ z hz
    simp only at e1 e2 ⊢
    rw [e1, e2, add_zero]
  funext y
  rw [filterMap_onB hB.1, runLayer_ctrlInstrs coinW_ne_caW _ (supp_of_avoid hB.1) hclean]
  cases hy : y (coinW d n)
  · simp only [Bool.false_eq_true, if_false]
    rw [Φ_coin_ne (b := true) (y := y) (by rw [hy]; decide), Φ_coin_ne (b := true) (y := y) (by rw [hy]; decide)]
  · simp only [if_true]
    rw [show (fun y => Φ false F (cnotFun (outD d n hd) (outW d n) y, μ) + Φ true B (y, μ)) =
      (fun y => Φ false F (cnotFun (outD d n hd) (outW d n) y, μ)) + (fun y => Φ true B (y, μ)) from rfl,
      runLayer_add, Pi.add_apply, hB.2,
      runLayer_vanish (fun g hg => (supp_of_avoid hB.1 g hg).1) (b := true)
        (fun z hz => Φ_coin_ne (by rw [hc, hz]; decide) μ) y hy,
      Φ_coin_ne (y := cnotFun (outD d n hd) (outW d n) y) (by rw [hc, hy]; decide) μ]

end ShiQIP
