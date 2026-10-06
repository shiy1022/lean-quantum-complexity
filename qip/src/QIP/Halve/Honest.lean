import QIP.Halve.Run


/-!
# Q31 — completeness of halving: the honest prover in the `d`-picture

The honest halved prover runs a clean unitary prover of `d` forward (coin `0`) or backward
(coin `1`) on the message wires. In the `d`-picture its states are the honest states of `d`
with some message registers *displaced* into the message wires (`dispF`, `dispB`).
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

/-! ## Layers and label maps with a parameter -/

section Locality

variable {M : ℕ} (D : Fin M → Prop)

/-- A layer avoiding `D` commutes with a label map changing only `D`, also when the state
depends on the `D`-part of the label. -/
theorem runLayer_comp_fam (f : Qubits M → Qubits M)
    (hf1 : ∀ y i b, ¬ D i → f (Function.update y i b) = Function.update (f y) i b)
    (hf2 : ∀ y i, ¬ D i → f y i = y i) :
    ∀ (l : List (Instr M)), (∀ g ∈ l, ∀ w ∈ g.support, ¬ D w) →
      ∀ Ψ : Qubits M → QState M, (∀ y i b, ¬ D i → Ψ (Function.update y i b) = Ψ y) →
        runLayer l (fun y => Ψ y (f y)) = fun y => runLayer l (Ψ y) (f y)
  | [], _, _, _ => rfl
  | g :: l, hl, Ψ, hΨ => by
    have hg : ∀ w ∈ g.support, ¬ D w := hl g List.mem_cons_self
    have step : g.apply (fun y => Ψ y (f y)) = fun y => g.apply (Ψ y) (f y) := by
      funext y
      cases g with
      | h i => simp only [Instr.support, Finset.mem_singleton, forall_eq] at hg
               simp only [Instr.apply, apply1, hf1 y i _ hg, hf2 y i hg, hΨ y i _ hg]
      | s i => simp only [Instr.support, Finset.mem_singleton, forall_eq] at hg
               simp only [Instr.apply, apply1, hf1 y i _ hg, hf2 y i hg, hΨ y i _ hg]
      | t i => simp only [Instr.support, Finset.mem_singleton, forall_eq] at hg
               simp only [Instr.apply, apply1, hf1 y i _ hg, hf2 y i hg, hΨ y i _ hg]
      | x i => simp only [Instr.support, Finset.mem_singleton, forall_eq] at hg
               simp only [Instr.apply, apply1, hf1 y i _ hg, hf2 y i hg, hΨ y i _ hg]
      | cnot i j hij =>
        have hi : ¬ D i := hg i (by simp [Instr.support])
        have hj : ¬ D j := hg j (by simp [Instr.support])
        change Ψ (cnotFun i j y) (f (cnotFun i j y)) = Ψ y (cnotFun i j (f y))
        simp only [cnotFun]
        rw [hΨ y j _ hj, hf1 y j _ hj, hf2 y i hi, hf2 y j hj]
    rw [runLayer_cons, step]
    have := runLayer_comp_fam f hf1 hf2 l (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
      (fun y => g.apply (Ψ y)) (fun y i b hi => by rw [hΨ y i b hi])
    rw [this]
    rfl

end Locality


/-! ## Honest states and turns in the `d`-picture -/

section Lift

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

variable (d n) in
/-- An honest state of `d` in the `d`-picture: coin copy `c`, message wires `0`. -/
def liftV (c : Bool) (ψ : Qubits d.totalWires × D → ℂ) : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ :=
  fun z => if z.2.1.1 = c ∧ ∀ u, z.2.2 u = false then ψ (z.1, z.2.1.2) else 0

variable (d n) in
/-- An honest turn of `d` (a matrix on register `t` and the memory) in the `d`-picture. -/
noncomputable def hon (t : ℕ) (U : Matrix (Reg d t × D) (Reg d t × D) ℂ)
    (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ) :
    Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ :=
  fun z => ∑ s : Reg d t, ∑ μ : D, U ((wireSplitE d t z.1).2, z.2.1.2) (s, μ) *
    v (PrefixData.regSet d t z.1 s, ((z.2.1.1, μ), z.2.2))

omit [DecidableEq D] in
theorem hon_liftV (t : ℕ) (U : Matrix (Reg d t × D) (Reg d t × D) ℂ) (c : Bool)
    (ψ : Qubits d.totalWires × D → ℂ) : hon d n t U (liftV d n c ψ) = liftV d n c (tv t U ψ) := by
  funext ⟨x, (c', μ'), β⟩
  simp only [hon, liftV, tv_apply]
  split_ifs with h
  · rfl
  · exact Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun μ _ => by rw [mul_zero]

theorem bOp_liftV (j : ℕ) (c : Bool) (ψ : Qubits d.totalWires × D → ℂ) :
    bOp d n (Bool × D) j (liftV d n c ψ) = liftV d n c ((blockMat d j ⊗ₖ (1 : Matrix D D ℂ)) *ᵥ ψ) := by
  funext ⟨x, (c', μ), β⟩
  simp only [bOp, blockOp, liftV]
  rw [kronOne_mulVec_apply, kronOne_mulVec_apply]
  split_ifs with h
  · congr 1; funext y'; simp only [liftV, if_pos h]
  · simp only [mulVec, dotProduct]
    exact Finset.sum_eq_zero fun x' _ => by simp only [liftV, if_neg h, mul_zero]

theorem bOpH_liftV (j : ℕ) (c : Bool) (ψ : Qubits d.totalWires × D → ℂ) :
    bOpH d n (Bool × D) j (liftV d n c ψ) =
      liftV d n c ((blockMat d j ⊗ₖ (1 : Matrix D D ℂ))ᴴ *ᵥ ψ) := by
  funext ⟨x, (c', μ), β⟩
  simp only [bOpH, blockOp, liftV, conjTranspose_kronecker, conjTranspose_one]
  rw [kronOne_mulVec_apply, kronOne_mulVec_apply]
  split_ifs with h
  · congr 1; funext y'; simp only [liftV, if_pos h]
  · simp only [mulVec, dotProduct]
    exact Finset.sum_eq_zero fun x' _ => by simp only [liftV, if_neg h, mul_zero]

end Lift

/-! ## Swaps commute with what they do not touch -/

section SwapComm

variable {d : Desc} {n : ℕ} {N₀ : Type} [Fintype N₀] [DecidableEq N₀]

omit [Fintype N₀] [DecidableEq N₀] in
theorem σSw_fst_of {p q r : ℕ} (z : Qubits d.totalWires × (N₀ × MB d n)) (w : Fin d.totalWires)
    (hw : ¬ (q ≤ (w : ℕ) ∧ (w : ℕ) < q + r)) : (σSw d n p q r z).1 w = z.1 w := by
  simp only [σSw]; rw [dif_neg (fun h => hw ⟨h.1, h.2.1⟩)]

omit [Fintype N₀] [DecidableEq N₀] in
theorem σSw_mem {p q r : ℕ} (z : Qubits d.totalWires × (N₀ × MB d n)) : (σSw d n p q r z).2.1 = z.2.1 := rfl

omit [Fintype N₀] [DecidableEq N₀] in
theorem σSw_snd_of {p q r : ℕ} (z : Qubits d.totalWires × (N₀ × MB d n)) (u : {w : Fin (halveDesc d n).totalWires //
    hPriv d ≤ (w : ℕ)}) (hu : ¬ (p ≤ (u.1 : ℕ) ∧ (u.1 : ℕ) < p + r)) : (σSw d n p q r z).2.2 u = z.2.2 u := by
  simp only [σSw]; rw [dif_neg (fun h => hu ⟨h.1, h.2.1⟩)]

/-- **A block of `d` commutes with a swap of wires it does not touch.** -/
theorem bOp_σSw {j p q r : ℕ} (hl : ∀ g ∈ dI d j, ∀ w ∈ g.support, ¬ (q ≤ (w : ℕ) ∧ (w : ℕ) < q + r))
    (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) :
    bOp d n N₀ j (v ∘ σSw d n p q r) = bOp d n N₀ j v ∘ σSw d n p q r := by
  funext ⟨x, ν⟩
  simp only [bOp, blockOp, Function.comp_apply]
  rw [kronOne_mulVec_apply, show σSw d n p q r (x, ν) = ((σSw d n p q r (x, ν)).1, (σSw d n p q r (x, ν)).2) from rfl,
    kronOne_mulVec_apply, blockMat, layerMat_mulVec, layerMat_mulVec]
  have := runLayer_comp_fam (fun w : Fin d.totalWires => q ≤ (w : ℕ) ∧ (w : ℕ) < q + r)
    (fun x' => (σSw d n p q r (x', ν)).1)
    (fun y i b hi => by
      funext w
      simp only [σSw, Function.update_apply]
      by_cases hw : w = i
      · subst hw; rw [dif_neg (fun h => hi ⟨h.1, h.2.1⟩)]; simp
      · simp only [if_neg hw])
    (fun y i hi => σSw_fst_of (y, ν) i hi) (dI d j) hl
    (fun x' => fun x'' => v (x'', (σSw d n p q r (x', ν)).2))
    (fun y i b hi => by
      funext x''
      congr 2
      simp only [σSw, Prod.mk.injEq, true_and]
      funext u
      split_ifs with h
      · rw [Function.update_of_ne]
        intro e; apply hi; rw [← e]; simp only; omega
      · rfl)
  exact congrFun this x

end SwapComm


/-! ## Slots of a message -/

section Slot

variable {d : Desc} {n : ℕ}

variable (d n) in
/-- Wire `w` is among the first `wd j` payload wires of message `k'`. -/
def slotIn (k j : ℕ) (w : Fin (halveDesc d n).totalWires) : Prop :=
  hPay d n k ≤ (w : ℕ) ∧ (w : ℕ) < hPay d n k + wd d j

instance (k j : ℕ) : DecidablePred (slotIn d n k j) := fun _ => by unfold slotIn; infer_instance

theorem inReg_halve_iff {k : ℕ} (hk : k ≤ n) (w : Fin (halveDesc d n).totalWires) :
    inReg (halveDesc d n) k w ↔ hOff d n k ≤ (w : ℕ) ∧ (w : ℕ) < hOff d n k + (hw d n k + if k = 1 then 1 else 0) := by
  unfold inReg
  rw [msgOffset_halveDesc d n k (by omega), width_hMsgs d n k hk]

theorem inReg_of_slotIn {k j : ℕ} (_hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k)
    {w : Fin (halveDesc d n).totalWires} (h : slotIn d n k j w) : inReg (halveDesc d n) k w := by
  rw [inReg_halve_iff hkn]
  unfold slotIn hPay at h
  split_ifs at h ⊢ <;> omega

variable (d n) in
/-- The wires of message `k'` outside the slot. -/
abbrev RestS (k j : ℕ) : Type :=
  {w : {w : Fin (halveDesc d n).totalWires // inReg (halveDesc d n) k w} // ¬ slotIn d n k j w.1} → Bool

variable (d n) in
/-- Split a label of message `k'` into the slot (a label of register `j` of `d`) and the rest. -/
def eS (k j : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k) :
    Reg (halveDesc d n) k ≃ RestS d n k j × Reg d j where
  toFun r := (fun w => r w.1, fun w => r ⟨⟨hPay d n k + (w.1 - d.msgOffset j), by
      have := w.2; unfold inReg at this; have := hPay_add_le hk1 hkn hj; unfold wd at *; omega⟩,
    inReg_of_slotIn hk1 hkn hj (by have := w.2; unfold inReg at this; unfold slotIn wd; simp only; omega)⟩)
  invFun p := fun w => if h : slotIn d n k j w.1 then p.2 ⟨⟨d.msgOffset j + (w.1 - hPay d n k), by
      have := msgOffset_add_width_le d j; unfold slotIn wd at h; unfold wd at *; omega⟩,
      by unfold inReg slotIn wd at *; simp only; omega⟩ else p.1 ⟨w, h⟩
  left_inv r := by
    funext w
    simp only
    split_ifs with h
    · congr 1; apply Subtype.ext; apply Fin.ext; simp only; unfold slotIn at h; omega
    · rfl
  right_inv p := by
    obtain ⟨ρ, s⟩ := p
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp only; rw [dif_neg w.2]
    · simp only
      rw [dif_pos (by have := w.2; unfold inReg at this; unfold slotIn wd; simp only; omega)]
      congr 1; apply Subtype.ext; apply Fin.ext; simp only; have := w.2; unfold inReg at this; omega

end Slot


/-! ## The honest turns of the halved prover -/

section HonestTurn

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

variable (d n D) in
/-- The reindexing behind `embU`. -/
def eSD (k j : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k) :
    Reg (halveDesc d n) k × D ≃ RestS d n k j × (Reg d j × D) :=
  ((eS d n k j hk1 hkn hj).prodCongr (Equiv.refl D)).trans (Equiv.prodAssoc _ _ _)

variable (d n) in
/-- A turn of `d` on register `j`, run on the slot of message `k'`. -/
noncomputable def embU (k j : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k)
    (U : Matrix (Reg d j × D) (Reg d j × D) ℂ) : Matrix (Reg (halveDesc d n) k × D) (Reg (halveDesc d n) k × D) ℂ :=
  ((1 : Matrix (RestS d n k j) (RestS d n k j) ℂ) ⊗ₖ U).submatrix (eSD d n D k j hk1 hkn hj) (eSD d n D k j hk1 hkn hj)

theorem embU_mem {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k)
    {U : Matrix (Reg d j × D) (Reg d j × D) ℂ} (hU : U ∈ Matrix.unitaryGroup _ ℂ) :
    embU d n k j hk1 hkn hj U ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (embU d n k j hk1 hkn hj U)ᴴ * embU d n k j hk1 hkn hj U = 1
  rw [embU, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]
  change ((1 : Matrix (RestS d n k j) (RestS d n k j) ℂ) ⊗ₖ (star U * U)).submatrix _ _ = 1
  rw [Matrix.mem_unitaryGroup_iff'.mp hU, one_kronecker_one]
  exact submatrix_one_equiv _

omit [Fintype D] [DecidableEq D] in
theorem embU_apply {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k)
    (U : Matrix (Reg d j × D) (Reg d j × D) ℂ) (a b : Reg (halveDesc d n) k) (m' m : D) :
    embU d n k j hk1 hkn hj U (a, m') (b, m) =
      if (eS d n k j hk1 hkn hj a).1 = (eS d n k j hk1 hkn hj b).1 then
        U ((eS d n k j hk1 hkn hj a).2, m') ((eS d n k j hk1 hkn hj b).2, m) else 0 := by
  simp only [embU, submatrix_apply, eSD, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq, Equiv.prodAssoc_apply, kroneckerMap_apply, one_apply]
  split_ifs <;> simp

variable {R : Type} [Fintype R] [DecidableEq R]

/-- A turn controlled by the coin copy kept in memory. -/
def ctl (E₀ E₁ : Matrix (R × D) (R × D) ℂ) : Matrix (R × (Bool × D)) (R × (Bool × D)) ℂ :=
  Matrix.of fun p q => if p.2.1 = q.2.1 then (if q.2.1 then E₁ else E₀) (p.1, p.2.2) (q.1, q.2.2) else 0

theorem ctl_mem {E₀ E₁ : Matrix (R × D) (R × D) ℂ} (h₀ : E₀ ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : E₁ ∈ Matrix.unitaryGroup _ ℂ) : ctl E₀ E₁ ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have e₀ := Matrix.mem_unitaryGroup_iff'.mp h₀
  have e₁ := Matrix.mem_unitaryGroup_iff'.mp h₁
  ext ⟨a, c₁, m₁⟩ ⟨b, c₂, m₂⟩
  change (∑ s, star (ctl E₀ E₁ s (a, c₁, m₁)) * ctl E₀ E₁ s (b, c₂, m₂)) = _
  simp only [ctl, of_apply, Fintype.sum_prod_type, Fintype.sum_bool, one_apply, Prod.mk.injEq]
  cases c₁ <;> cases c₂ <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.true_eq_false, star_zero,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, false_and, and_false, true_and]
  · have := congrFun (congrFun e₀ (a, m₁)) (b, m₂)
    rw [mul_apply, Fintype.sum_prod_type] at this
    simpa [one_apply] using this
  · have := congrFun (congrFun e₁ (a, m₁)) (b, m₂)
    rw [mul_apply, Fintype.sum_prod_type] at this
    simpa [one_apply] using this

end HonestTurn


/-! ## Transport: the honest prover turn is a conjugated turn of `d` -/

section Transport

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem proverOp_ctl_apply {k : ℕ} (E₀ E₁ : Matrix (Reg (halveDesc d n) k × D) (Reg (halveDesc d n) k × D) ℂ)
    (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ) (x : Qubits d.totalWires) (c' : Bool) (m' : D)
    (β : MB d n) :
    proverOp d n (Bool × D) k (ctl E₀ E₁) v (x, ((c', m'), β)) =
      ∑ r : Reg (halveDesc d n) k, ∑ m : D, (if c' then E₁ else E₀) ((mbSplit d n k β).2, m') (r, m) *
        v (x, ((c', m), (mbSplit d n k).symm ((mbSplit d n k β).1, r))) := by
  simp only [proverOp]
  rw [one_kron_mulVec_apply, PA_mulVec]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases c' <;> simp [ctl]

omit [DecidableEq D] in
theorem sum_embU {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k)
    (U : Matrix (Reg d j × D) (Reg d j × D) ℂ) (a : Reg (halveDesc d n) k) (m' : D)
    (f : Reg (halveDesc d n) k → D → ℂ) :
    ∑ r, ∑ m, embU d n k j hk1 hkn hj U (a, m') (r, m) * f r m =
      ∑ s, ∑ m, U ((eS d n k j hk1 hkn hj a).2, m') (s, m) *
        f ((eS d n k j hk1 hkn hj).symm ((eS d n k j hk1 hkn hj a).1, s)) m := by
  rw [← Equiv.sum_comp (eS d n k j hk1 hkn hj).symm, Fintype.sum_prod_type,
    Finset.sum_eq_single (eS d n k j hk1 hkn hj a).1]
  · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun m _ => ?_
    rw [embU_apply, Equiv.apply_symm_apply, if_pos rfl]
  · intro ρ _ hρ
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun m _ => ?_
    rw [embU_apply, Equiv.apply_symm_apply, if_neg (Ne.symm hρ), zero_mul]
  · simp

omit [DecidableEq D] in
/-- **Transport**: on coin copy `c`, the honest prover turn on message `k'` is the turn `U` of `d`
on register `j`, conjugated by the swap of register `j` with the slot of message `k'`. -/
theorem transport {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k)
    (U : Matrix (Reg d j × D) (Reg d j × D) ℂ) (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ)
    (x : Qubits d.totalWires) (c' : Bool) (m' : D) (β : MB d n) :
    (∑ r : Reg (halveDesc d n) k, ∑ m : D, embU d n k j hk1 hkn hj U ((mbSplit d n k β).2, m') (r, m) *
        v (x, ((c', m), (mbSplit d n k).symm ((mbSplit d n k β).1, r)))) =
      hon d n j U (v ∘ σSw d n (hPay d n k) (d.msgOffset j) (wd d j))
        (σSw d n (hPay d n k) (d.msgOffset j) (wd d j) (x, ((c', m'), β))) := by
  have h1 := msgOffset_add_width_le d j
  have h2 := hPay_ge (d := d) (n := n) k
  have h3 := hPay_add_le hk1 hkn hj
  have hW : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have hr : wd d j = d.msgWidth j := rfl
  rw [sum_embU]
  simp only [hon, Function.comp_apply]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · -- the register read by `U`
    congr 2
    funext w
    simp only [eS, Equiv.coe_fn_mk, wireSplitE, Equiv.trans_apply, Equiv.piEquivPiSubtypeProd_apply,
      Equiv.prodComm_apply, Prod.snd_swap, mbSplit, σSw]
    have hw := w.2
    unfold inReg at hw
    rw [dif_pos ⟨hw.1, by omega, h2, h3⟩]
  · -- the label after the turn
    congr 1
    refine Prod.ext (funext fun w => ?_) (Prod.ext rfl (funext fun u => ?_))
    · simp only [σSw, PrefixData.regSet_apply]
      split_ifs <;> (try unfold inReg at *) <;> first
        | rfl
        | (exfalso; omega)
        | (congr 1; apply Fin.ext; simp only; omega)
    · simp only [σSw, mbSplit, Equiv.coe_fn_symm_mk, eS, Equiv.coe_fn_mk, PrefixData.regSet_apply]
      have hu := u.2
      have hk0 : (halveDesc d n).msgOffset k ≤ hPay d n k ∧
          hPay d n k + hw d n k ≤ (halveDesc d n).msgOffset k + (halveDesc d n).msgWidth k := by
        rw [msgOffset_halveDesc d n k (by omega), width_hMsgs d n k hkn]
        unfold hPay; split_ifs <;> omega
      split_ifs <;> (try unfold inReg at *) <;> (try unfold slotIn at *) <;> first
        | rfl
        | (exfalso; omega)
        | (exfalso; simp only at *; omega)

end Transport


section Transport2

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

/-- The swap of message `k'` with register `j`, on `d`-picture labels. -/
abbrev swL (k j : ℕ) : Qubits d.totalWires × ((Bool × D) × MB d n) → Qubits d.totalWires × ((Bool × D) × MB d n) :=
  σSw d n (hPay d n k) (d.msgOffset j) (wd d j)

omit [DecidableEq D] in
/-- **Transport, as operators**, on states with coin copy `c`. -/
theorem proverOp_ctl {k j₀ j₁ : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (h₀ : wd d j₀ ≤ hw d n k)
    (h₁ : wd d j₁ ≤ hw d n k) (U₀ : Matrix (Reg d j₀ × D) (Reg d j₀ × D) ℂ)
    (U₁ : Matrix (Reg d j₁ × D) (Reg d j₁ × D) ℂ) (c : Bool)
    (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ) (hv : ∀ z, z.2.1.1 ≠ c → v z = 0) :
    proverOp d n (Bool × D) k (ctl (embU d n k j₀ hk1 hkn h₀ U₀) (embU d n k j₁ hk1 hkn h₁ U₁)) v =
      if c then hon d n j₁ U₁ (v ∘ swL k j₁) ∘ swL k j₁ else hon d n j₀ U₀ (v ∘ swL k j₀) ∘ swL k j₀ := by
  funext ⟨x, (c', m'), β⟩
  rw [proverOp_ctl_apply]
  by_cases hc : c' = c
  · subst hc
    cases c' <;> simp only [if_true, if_false, Bool.false_eq_true, Function.comp_apply] <;> exact transport _ _ _ _ _ _ _ _ _
  · rw [Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun m _ => by rw [hv _ hc, mul_zero]]
    have hz : ∀ j (U : Matrix (Reg d j × D) (Reg d j × D) ℂ) (k' : ℕ),
        hon d n j U (v ∘ swL k' j) (swL k' j (x, ((c', m'), β))) = 0 := by
      intro j U k'
      simp only [hon]
      exact Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun m _ => by
        rw [Function.comp_apply, hv _ hc, mul_zero]
    cases c <;> simp only [if_true, if_false, Bool.false_eq_true, Function.comp_apply, hz]

omit [DecidableEq D] in
/-- **The honest turn commutes with a swap elsewhere.** -/
theorem hon_sw {t k j : ℕ} (hdis : ∀ w : Fin d.totalWires, d.msgOffset j ≤ (w : ℕ) → (w : ℕ) < d.msgOffset j + wd d j →
      ¬ inReg d t w) (U : Matrix (Reg d t × D) (Reg d t × D) ℂ)
    (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ) :
    hon d n t U (v ∘ swL k j) = hon d n t U v ∘ swL k j := by
  funext ⟨x, (c, m'), β⟩
  simp only [hon, Function.comp_apply]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · congr 2
    funext w
    simp only [wireSplitE, Equiv.trans_apply, Equiv.piEquivPiSubtypeProd_apply, Equiv.prodComm_apply,
      Prod.snd_swap, σSw]
    rw [dif_neg]
    intro h
    exact hdis w.1 h.1 h.2.1 w.2
  · congr 1
    refine Prod.ext (funext fun w => ?_) (Prod.ext rfl (funext fun u => ?_))
    · simp only [σSw, PrefixData.regSet_apply]
      split_ifs with h1 h2 h2
      · exact absurd h2 (hdis w h1.1 h1.2.1)
      · rfl
      · rfl
      · rfl
    · simp only [σSw, PrefixData.regSet_apply]
      split_ifs with h1 h2
      · exact absurd h2 (hdis _ (by simp only; omega) (by simp only; omega))
      · rfl
      · rfl

omit [DecidableEq D] in
omit [Fintype D] in
/-- A state vanishing unless register `j` and the slot of message `k'` read `0` is swap-invariant. -/
theorem comp_sw_of_zero {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k)
    (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ)
    (hv : ∀ z : Qubits d.totalWires × ((Bool × D) × MB d n),
      (∃ w : Fin d.totalWires, d.msgOffset j ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset j + wd d j ∧ z.1 w = true) ∨
      (∃ u : {w : Fin (halveDesc d n).totalWires // hPriv d ≤ (w : ℕ)},
        hPay d n k ≤ (u.1 : ℕ) ∧ (u.1 : ℕ) < hPay d n k + wd d j ∧ z.2.2 u = true) → v z = 0) :
    v ∘ swL k j = v := by
  have h1 := msgOffset_add_width_le d j
  have h2 := hPay_ge (d := d) (n := n) k
  have h3 := hPay_add_le hk1 hkn hj
  have hr : wd d j = d.msgWidth j := rfl
  funext z
  simp only [Function.comp_apply]
  by_cases hz : (∃ w : Fin d.totalWires, d.msgOffset j ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset j + wd d j ∧ z.1 w = true) ∨
      (∃ u : {w : Fin (halveDesc d n).totalWires // hPriv d ≤ (w : ℕ)},
        hPay d n k ≤ (u.1 : ℕ) ∧ (u.1 : ℕ) < hPay d n k + wd d j ∧ z.2.2 u = true)
  · rw [hv z hz]
    apply hv
    rcases hz with ⟨w, hw1, hw2, hw⟩ | ⟨u, hu1, hu2, hu⟩
    · right
      refine ⟨⟨⟨hPay d n k + (w - d.msgOffset j), by omega⟩, by (try simp only); omega⟩, by (try simp only); omega,
        by (try simp only); omega, ?_⟩
      simp only [σSw]
      rw [dif_pos ⟨by omega, by omega, by omega⟩]
      convert hw using 2
      apply Fin.ext; simp only; omega
    · left
      refine ⟨⟨d.msgOffset j + (u.1 - hPay d n k), by omega⟩, by (try simp only); omega, by (try simp only); omega, ?_⟩
      simp only [σSw]
      rw [dif_pos ⟨by omega, by omega, h2, h3⟩]
      convert hu using 2
      apply Subtype.ext; apply Fin.ext; simp only; omega
  · push Not at hz
    congr 1
    obtain ⟨x, ν, β⟩ := z
    simp only [σSw, Prod.mk.injEq, true_and]
    refine ⟨funext fun w => ?_, funext fun u => ?_⟩
    · split_ifs with h
      · have e1 := hz.2 ⟨⟨hPay d n k + (w - d.msgOffset j), by omega⟩, by (try simp only); omega⟩
          (by (try simp only); omega) (by (try simp only); omega)
        have e2 := hz.1 w h.1 h.2.1
        simp only [Bool.not_eq_true] at e1 e2
        rw [e1, e2]
      · rfl
    · split_ifs with h
      · have e1 := hz.1 ⟨d.msgOffset j + (u.1 - hPay d n k), by omega⟩ (by (try simp only); omega) (by (try simp only); omega)
        have e2 := hz.2 u h.1 h.2.1
        simp only [Bool.not_eq_true] at e1 e2
        rw [e1, e2]
      · rfl

end Transport2


/-! ## The honest run of `d` -/

section DRun

variable {d : Desc} {D : Type} [Fintype D] [DecidableEq D]

variable (d D) in
/-- The run of `d` against unitary turns `U` with constant memory `D`. -/
noncomputable def dRun (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (ι : D → ℂ) :
    ℕ → Qubits d.totalWires × D → ℂ
  | 0 => (blockMat d 0 ⊗ₖ (1 : Matrix D D ℂ)) *ᵥ fun p => zeroVec d.totalWires p.1 * ι p.2
  | t + 1 => (blockMat d (t + 1) ⊗ₖ (1 : Matrix D D ℂ)) *ᵥ tv t (U t) (dRun U ι t)

theorem pureRun_dilateU_dRun (T : IsoStrategy (Reg d) (Reg d) d.numMsgs) :
    ∀ t, pureRun (dilateU T) t = dRun d (DilMem d T) (dilU T) (dilateU T).init t
  | 0 => rfl
  | t + 1 => by rw [pureRun, dRun, ← pureRun_dilateU_dRun T t]; rfl

/-- A block avoiding wire `w` keeps states vanishing when `w` reads `1`. -/
theorem kron_vanish {j : ℕ} (hd : d.Valid) {w : Fin d.totalWires} (hw : d.held j w = false)
    (ψ : Qubits d.totalWires × D → ℂ) (hψ : ∀ x μ, x w = true → ψ (x, μ) = 0) :
    ∀ x μ, x w = true → ((blockMat d j ⊗ₖ (1 : Matrix D D ℂ)) *ᵥ ψ) (x, μ) = 0 := by
  intro x μ hx
  rw [kronOne_mulVec_apply, blockMat, layerMat_mulVec]
  have hl : ∀ g ∈ dI d j, w ∉ g.support := fun g hg hw' => by
    have := hd.support_held j g hg w hw'
    rw [hw] at this; exact Bool.false_ne_true this
  have h := runLayer_sliceEq (w := w) (b := true) (dI d j) hl (φ := fun x' => ψ (x', μ)) (φ' := 0)
    (fun z hz => by show ψ (z, μ) = 0; exact hψ z μ hz)
  rw [show (d.blocks.getD j []).filterMap (Gate.toInstr? d.totalWires) = dI d j from rfl, h x hx]
  rw [← layerMat_mulVec, mulVec_zero]; rfl

theorem support_instrInv {M : ℕ} {g g' : Instr M} (h : g' ∈ instrInv g) : g'.support = g.support := by
  cases g with
  | h i => simp only [instrInv, List.mem_singleton] at h; subst h; rfl
  | s i => simp only [instrInv, List.mem_cons, List.not_mem_nil, or_false, or_self] at h; subst h; rfl
  | t i => rw [instrInv, List.mem_replicate] at h; obtain ⟨-, rfl⟩ := h; rfl
  | x i => simp only [instrInv, List.mem_singleton] at h; subst h; rfl
  | cnot i j hij => simp only [instrInv, List.mem_singleton] at h; subst h; rfl

theorem kronH_vanish {j : ℕ} (hd : d.Valid) {w : Fin d.totalWires} (hw : d.held j w = false)
    (ψ : Qubits d.totalWires × D → ℂ) (hψ : ∀ x μ, x w = true → ψ (x, μ) = 0) :
    ∀ x μ, x w = true → ((blockMat d j ⊗ₖ (1 : Matrix D D ℂ))ᴴ *ᵥ ψ) (x, μ) = 0 := by
  intro x μ hx
  rw [conjTranspose_kronecker, conjTranspose_one, kronOne_mulVec_apply, blockMat, ← layerMat_adjointInstrs,
    layerMat_mulVec]
  have hl : ∀ g ∈ adjointInstrs (dI d j), w ∉ g.support := by
    intro g hg hw'
    simp only [adjointInstrs, List.mem_flatten, List.mem_map, List.mem_reverse] at hg
    obtain ⟨l, ⟨g₀, hg₀, rfl⟩, hgl⟩ := hg
    have hs : w ∈ g₀.support := by rw [← support_instrInv hgl]; exact hw'
    have := hd.support_held j g₀ hg₀ w hs
    rw [hw] at this; exact Bool.false_ne_true this
  have h := runLayer_sliceEq (w := w) (b := true) (adjointInstrs (dI d j)) hl (φ := fun x' => ψ (x', μ))
    (φ' := 0) (fun z hz => by show ψ (z, μ) = 0; exact hψ z μ hz)
  change runLayer (adjointInstrs (dI d j)) _ x = 0
  rw [h x hx, ← layerMat_mulVec, mulVec_zero]; rfl

omit [DecidableEq D] in
/-- A turn on register `t` keeps states vanishing when a wire outside register `t` reads `1`. -/
theorem tv_vanish {t : ℕ} (A : Matrix (Reg d t × D) (Reg d t × D) ℂ) {w : Fin d.totalWires}
    (hw : ¬ inReg d t w) (ψ : Qubits d.totalWires × D → ℂ) (hψ : ∀ x μ, x w = true → ψ (x, μ) = 0) :
    ∀ x μ, x w = true → tv t A ψ (x, μ) = 0 := by
  intro x μ hx
  rw [tv_apply]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun m _ => ?_
  rw [hψ _ _ (by rw [PrefixData.regSet_apply, dif_neg hw]; exact hx), mul_zero]

theorem held_toV_le {i b : ℕ} (hp : ¬ toProverAt d i) (hb : b ≤ i) {w : Fin d.totalWires} (hw : inReg d i w) :
    d.held b w = false := by
  rw [Bool.eq_false_iff, ne_eq, held_iff]
  rintro (h | ⟨i', hi', hdir⟩)
  · exact not_priv_of_inReg hw h
  · obtain rfl := inReg_unique hi' hw
    have hv : (d.msgs.map Message.dir).getD i' .toVerifier = .toVerifier := by
      unfold toProverAt at hp
      cases h : (d.msgs.map Message.dir).getD i' .toVerifier
      · rfl
      · exact absurd h hp
    rw [hv] at hdir
    simp [dirOk] at hdir
    omega

/-- **Registers of later messages to the verifier still read `0`.** -/
theorem dRun_future (hd : d.Valid) (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (ι : D → ℂ) {i : ℕ}
    (hp : ¬ toProverAt d i) {w : Fin d.totalWires} (hw : inReg d i w) :
    ∀ t, t ≤ i → ∀ x μ, x w = true → dRun d D U ι t (x, μ) = 0
  | 0, _ => kron_vanish hd (held_toV_le hp (Nat.zero_le _) hw) _ (fun x μ hx => by
      simp only [zeroVec]; rw [if_neg (fun h => by rw [h] at hx; exact Bool.false_ne_true hx), zero_mul])
  | t + 1, ht => kron_vanish hd (held_toV_le hp ht hw) _
      (tv_vanish _ (fun h => by have := inReg_unique h hw; omega) _
        (dRun_future hd U ι hp hw t (by omega)))

end DRun


/-! ## Displaced registers -/

section Disp

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

variable (d n D) in
/-- Displace the registers `reg (f k)` (for the `k ≤ j` with `P k`) into the slots of messages `k'`. -/
def disp (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ℕ → Qubits d.totalWires × ((Bool × D) × MB d n) → Qubits d.totalWires × ((Bool × D) × MB d n)
  | 0 => id
  | k + 1 => if P (k + 1) then disp f P k ∘ swL (k + 1) (f (k + 1)) else disp f P k

variable (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]

/-- Displaced wires of `d`. -/
def DispW (d : Desc) (f : ℕ → ℕ) (P : ℕ → Prop) (j : ℕ) (w : Fin d.totalWires) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ j ∧ P k ∧ d.msgOffset (f k) ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset (f k) + wd d (f k)

/-- Displaced slots. -/
def DispS (d : Desc) (n : ℕ) (f : ℕ → ℕ) (P : ℕ → Prop) (j : ℕ) (u : Fin (halveDesc d n).totalWires) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ j ∧ P k ∧ hPay d n k ≤ (u : ℕ) ∧ (u : ℕ) < hPay d n k + wd d (f k)

omit [Fintype D] [DecidableEq D] in
theorem disp_mem : ∀ j z, (disp d n D f P j z).2.1 = z.2.1
  | 0, _ => rfl
  | k + 1, z => by
    simp only [disp]
    split_ifs
    · exact (disp_mem k _).trans (σSw_mem z)
    · exact disp_mem k z

omit [Fintype D] [DecidableEq D] in
theorem disp_fst : ∀ j z (w : Fin d.totalWires), ¬ DispW d f P j w → (disp d n D f P j z).1 w = z.1 w
  | 0, _, _, _ => rfl
  | k + 1, z, w, hw => by
    simp only [disp]
    split_ifs with hP
    · simp only [Function.comp_apply]
      rw [disp_fst k _ w (fun ⟨k', h1, h2, h3, h4⟩ => hw ⟨k', h1, by omega, h3, h4⟩)]
      exact σSw_fst_of z w (fun h => hw ⟨k + 1, by omega, le_rfl, hP, h⟩)
    · exact disp_fst k z w (fun ⟨k', h1, h2, h3, h4⟩ => hw ⟨k', h1, by omega, h3, h4⟩)

omit [Fintype D] [DecidableEq D] in
theorem disp_snd : ∀ j z (u : {w : Fin (halveDesc d n).totalWires // hPriv d ≤ (w : ℕ)}),
    ¬ DispS d n f P j u.1 → (disp d n D f P j z).2.2 u = z.2.2 u
  | 0, _, _, _ => rfl
  | k + 1, z, u, hu => by
    simp only [disp]
    split_ifs with hP
    · simp only [Function.comp_apply]
      rw [disp_snd k _ u (fun ⟨k', h1, h2, h3, h4⟩ => hu ⟨k', h1, by omega, h3, h4⟩)]
      exact σSw_snd_of z u (fun h => hu ⟨k + 1, by omega, le_rfl, hP, h⟩)
    · exact disp_snd k z u (fun ⟨k', h1, h2, h3, h4⟩ => hu ⟨k', h1, by omega, h3, h4⟩)

/-- **Blocks commute with displacement** of registers they do not touch. -/
theorem bOp_disp {t : ℕ} : ∀ j, (∀ k, 1 ≤ k → k ≤ j → P k → ∀ g ∈ dI d t, ∀ w ∈ g.support,
      ¬ (d.msgOffset (f k) ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset (f k) + wd d (f k))) →
    ∀ L : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ,
      bOp d n (Bool × D) t (L ∘ disp d n D f P j) = bOp d n (Bool × D) t L ∘ disp d n D f P j
  | 0, _, L => rfl
  | k + 1, h, L => by
    simp only [disp]
    split_ifs with hP
    · rw [← Function.comp_assoc, bOp_σSw (h (k + 1) (by omega) le_rfl hP),
        bOp_disp k (fun k' h1 h2 h3 => h k' h1 (by omega) h3), Function.comp_assoc]
    · exact bOp_disp k (fun k' h1 h2 h3 => h k' h1 (by omega) h3) L

omit [DecidableEq D] in
/-- **The honest turn commutes with displacement** of other registers. -/
theorem hon_disp {t : ℕ} (U : Matrix (Reg d t × D) (Reg d t × D) ℂ) : ∀ j,
    (∀ k, 1 ≤ k → k ≤ j → P k → ∀ w : Fin d.totalWires, d.msgOffset (f k) ≤ (w : ℕ) →
      (w : ℕ) < d.msgOffset (f k) + wd d (f k) → ¬ inReg d t w) →
    ∀ L : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ,
      hon d n t U (L ∘ disp d n D f P j) = hon d n t U L ∘ disp d n D f P j
  | 0, _, L => rfl
  | k + 1, h, L => by
    simp only [disp]
    split_ifs with hP
    · rw [← Function.comp_assoc, hon_sw (h (k + 1) (by omega) le_rfl hP),
        hon_disp U k (fun k' h1 h2 h3 => h k' h1 (by omega) h3), Function.comp_assoc]
    · exact hon_disp U k (fun k' h1 h2 h3 => h k' h1 (by omega) h3) L

omit [DecidableEq D] in
/-- **Displacement preserves weighted norms** for weights not seeing the displaced wires. -/
theorem sum_disp : ∀ j, (∀ k, 1 ≤ k → k ≤ j → P k → k ≤ n ∧ wd d (f k) ≤ hw d n k) →
      ∀ g : Qubits d.totalWires × ((Bool × D) × MB d n) → ℝ,
      (∀ k, 1 ≤ k → k ≤ j → P k → ∀ z, g (swL k (f k) z) = g z) →
      ∀ v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ,
        ∑ z, g z * ‖v (disp d n D f P j z)‖ ^ 2 = ∑ z, g z * ‖v z‖ ^ 2
  | 0, _, _, _, _ => rfl
  | k + 1, hb, g, hg, v => by
    simp only [disp]
    split_ifs with hP
    · obtain ⟨h2, h3⟩ := hb (k + 1) (by omega) le_rfl hP
      have hinv := σSw_involutive (N₀ := Bool × D) (d := d) (n := n)
        (show d.msgOffset (f (k + 1)) + wd d (f (k + 1)) ≤ d.totalWires from msgOffset_add_width_le d _)
        (hPay_ge (k + 1)) (hPay_add_le (by omega) h2 h3)
      simp only [Function.comp_apply]
      rw [← sum_invol hinv (fun z => g z * ‖v (disp d n D f P k (swL (k + 1) (f (k + 1)) z))‖ ^ 2)]
      simp only [hinv _, hg (k + 1) (by omega) le_rfl hP]
      exact sum_disp k (fun k' h1 h2 h3 => hb k' h1 (by omega) h3) g
        (fun k' h1 h2 h3 => hg k' h1 (by omega) h3) v
    · exact sum_disp k (fun k' h1 h2 h3 => hb k' h1 (by omega) h3) g
        (fun k' h1 h2 h3 => hg k' h1 (by omega) h3) v

end Disp


/-! ## The coin copy moves into the prover's memory -/

section Copy

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

variable (d n D) in
/-- Swap the coin-copy wire (if it belongs to message `k'`) with the memory bit. -/
def cpy (k : ℕ) (p : Reg (halveDesc d n) k × (Bool × D)) : Reg (halveDesc d n) k × (Bool × D) :=
  if h : inReg (halveDesc d n) k (copyW d n) then
    (Function.update p.1 ⟨copyW d n, h⟩ p.2.1, (p.1 ⟨copyW d n, h⟩, p.2.2)) else p

omit [Fintype D] [DecidableEq D] in
theorem cpy_involutive (k : ℕ) : Function.Involutive (cpy d n D k) := by
  intro p
  obtain ⟨r, c, μ⟩ := p
  by_cases h : inReg (halveDesc d n) k (copyW d n)
  · simp only [cpy, dif_pos h, Function.update_self, Function.update_idem, Function.update_eq_self]
  · simp only [cpy, dif_neg h]

variable (d n D) in
/-- The coin-copy swap as a permutation. -/
def cpyPerm (k : ℕ) : Equiv.Perm (Reg (halveDesc d n) k × (Bool × D)) :=
  Function.Involutive.toPerm _ (cpy_involutive (d := d) (n := n) (D := D) k)

variable (d n D) in
/-- The coin-copy swap on `d`-picture labels. -/
def cpyL (k : ℕ) (z : Qubits d.totalWires × ((Bool × D) × MB d n)) : Qubits d.totalWires × ((Bool × D) × MB d n) :=
  if h : inReg (halveDesc d n) k (copyW d n) then
    (z.1, ((z.2.2 ⟨copyW d n, hPriv_le_of_inReg h⟩, z.2.1.2),
      fun u => if u.1 = copyW d n then z.2.1.1 else z.2.2 u)) else z

omit [DecidableEq D] in
theorem PA_mul {k : ℕ} (A B : Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ) :
    PA d n k (A * B) = PA d n k A * PA d n k B := by
  rw [PA, PA, PA, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

omit [DecidableEq D] in
theorem proverOp_mul {k : ℕ}
    (A B : Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ)
    (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ) :
    proverOp d n (Bool × D) k (A * B) v = proverOp d n (Bool × D) k A (proverOp d n (Bool × D) k B v) := by
  simp only [proverOp, PA_mul, mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul]

theorem proverOp_cpy (k : ℕ) (v : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ) :
    proverOp d n (Bool × D) k (pmat (cpyPerm d n D k)) v = v ∘ cpyL d n D k := by
  funext ⟨x, (c', m'), β⟩
  simp only [proverOp]
  rw [one_kron_mulVec_apply, PA_mulVec, ← Fintype.sum_prod_type',
    Finset.sum_eq_single (cpy d n D k ((mbSplit d n k β).2, (c', m')))]
  · have e : (((mbSplit d n k) β).2, (c', m')) = cpyPerm d n D k (cpy d n D k (((mbSplit d n k) β).2, (c', m'))) :=
      (cpy_involutive k _).symm
    simp only [pmat, of_apply]
    rw [if_pos e, one_mul, Function.comp_apply]
    congr 1
    simp only [cpyL, cpy]
    split_ifs with h
    · refine Prod.ext rfl (Prod.ext rfl (funext fun u => ?_))
      simp only [mbSplit, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Function.update_apply]
      by_cases h1 : u.1 = copyW d n
      · have hr : inReg (halveDesc d n) k u.1 := h1 ▸ h
        rw [dif_pos hr, if_pos (Subtype.ext h1), if_pos h1]
      · rw [if_neg h1]
        split_ifs with h2 h3
        · exact absurd (congrArg Subtype.val h3) h1
        · rfl
        · rfl
    · refine Prod.ext rfl (Prod.ext rfl (funext fun u => ?_))
      simp only [mbSplit, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
      split_ifs <;> rfl
  · intro b _ hb
    simp only [pmat, of_apply]
    rw [if_neg, zero_mul]
    intro e
    apply hb
    rw [e]
    exact (cpy_involutive k _).symm
  · simp

end Copy


/-! ## Support facts -/

section Supp

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

theorem toP_iff_odd (hsch : d.HasSchedule (2 * n + 1)) {i : ℕ} (hi : i < 2 * n + 1) :
    toProverAt d i ↔ i % 2 = 1 := by
  unfold toProverAt
  rw [hsch, stdSchedule, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  split_ifs with h
  · simp only [false_iff]; omega
  · simp only [true_iff]; omega

theorem copyW_lt_hPay (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) : ((copyW d n : Fin _) : ℕ) < hPay d n k := by
  rw [copyW_val hn]
  unfold hPay
  by_cases h : k = 1
  · subst h; simp
  · rw [if_neg h]
    have h1 := hOff_mono d n (show 2 ≤ k by omega)
    have h2 : hOff d n 2 = hOff d n 1 + (hw d n 1 + 1) := by simpa using hOff_succ d n 1
    omega

omit [Fintype D] [DecidableEq D] in
theorem cpyL_fix (k : ℕ) (z : Qubits d.totalWires × ((Bool × D) × MB d n))
    (h : ∀ hc : inReg (halveDesc d n) k (copyW d n), z.2.1.1 = z.2.2 ⟨copyW d n, hPriv_le_of_inReg hc⟩) :
    cpyL d n D k z = z := by
  obtain ⟨x, ⟨c, μ⟩, β⟩ := z
  simp only [cpyL]
  split_ifs with hc
  · have e := h hc
    simp only at e
    refine Prod.ext rfl (Prod.ext (Prod.ext e.symm rfl) (funext fun u => ?_))
    simp only
    split_ifs with hu
    · rw [e]; congr 1; exact Subtype.ext hu.symm
    · rfl
  · rfl

omit [Fintype D] [DecidableEq D] in
/-- A state with coin copy `0` in memory and on the copy wire is fixed by the coin-copy swap. -/
theorem comp_cpyL (k : ℕ) (w : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ)
    (hw : ∀ z : Qubits d.totalWires × ((Bool × D) × MB d n), z.2.1.1 = true ∨
      (∃ h : hPriv d ≤ ((copyW d n : Fin _) : ℕ), z.2.2 ⟨copyW d n, h⟩ = true) → w z = 0) :
    w ∘ cpyL d n D k = w := by
  funext z
  simp only [Function.comp_apply]
  by_cases hc : inReg (halveDesc d n) k (copyW d n)
  · by_cases e : z.2.1.1 = z.2.2 ⟨copyW d n, hPriv_le_of_inReg hc⟩
    · rw [cpyL_fix k z (fun _ => e)]
    · have hz : w z = 0 := by
        apply hw
        cases h1 : z.2.1.1
        · right; refine ⟨hPriv_le_of_inReg hc, ?_⟩; rw [h1] at e; simpa using (Ne.symm e)
        · left; rfl
      rw [hz]
      apply hw
      obtain ⟨x, ⟨c, μ⟩, β⟩ := z
      simp only [cpyL, dif_pos hc] at e ⊢
      cases hcz : c
      · left; rw [hcz] at e; simpa using (Ne.symm e)
      · right; exact ⟨hPriv_le_of_inReg hc, by simp⟩
  · rw [show cpyL d n D k z = z by simp only [cpyL, dif_neg hc]]

end Supp


/-! ## The forward branch of the honest prover -/

section Forward

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

variable (d n D) in
/-- The honest halved prover's turn `k'` (`1 ≤ k ≤ n`). -/
noncomputable def honA (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ :=
  ctl (embU d n k (n + k) hk1 hkn (wd_le_hw_fwd hk1) (U (n + k)))
    (embU d n k (n + 1 - k) hk1 hkn (wd_le_hw_bwd hk1) (U (n + 1 - k))ᴴ) * pmat (cpyPerm d n D k)

/-- Forward displacement: the messages `n + k` to the prover (`k` odd) sit in the slots. -/
abbrev dispF (d : Desc) (n : ℕ) (D : Type) [Fintype D] [DecidableEq D] (j : ℕ) :=
  disp d n D (fun k => n + k) (fun k => k % 2 = 1) j

omit [Fintype D] [DecidableEq D] in
theorem liftV_vanish {c : Bool} {ψ : Qubits d.totalWires × D → ℂ} {z : Qubits d.totalWires × ((Bool × D) × MB d n)}
    (h : z.2.1.1 ≠ c ∨ ∃ u, z.2.2 u = true) : liftV d n c ψ z = 0 := by
  simp only [liftV]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rcases h with h | ⟨u, hu⟩
  · exact h h1
  · rw [h2 u] at hu; exact Bool.false_ne_true hu

theorem copy_not_dispS (hn : 1 ≤ n) (f : ℕ → ℕ) (P : ℕ → Prop) (j : ℕ) : ¬ DispS d n f P j (copyW d n) :=
  fun ⟨k, h1, _, _, h4, _⟩ => by have := copyW_lt_hPay (d := d) hn h1; omega


theorem region_not_inReg {i i' : ℕ} (hii : i ≠ i') {w : Fin d.totalWires}
    (h1 : d.msgOffset i ≤ (w : ℕ)) (h2 : (w : ℕ) < d.msgOffset i + wd d i) : ¬ inReg d i' w :=
  fun h => hii (inReg_unique ⟨h1, h2⟩ h)

theorem dI_avoid_dead (hd : d.Valid) {i t : ℕ} (hp : toProverAt d i) (hlt : i < t) :
    ∀ g ∈ dI d t, ∀ w ∈ g.support, ¬ (d.msgOffset i ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset i + wd d i) := by
  intro g hg w hw hr
  have := hd.support_held t g hg w hw
  rw [not_held_of_dead hlt hp hr] at this
  exact Bool.false_ne_true this

theorem dI_avoid_future (hd : d.Valid) {i t : ℕ} (hp : ¬ toProverAt d i) (hle : t ≤ i) :
    ∀ g ∈ dI d t, ∀ w ∈ g.support, ¬ (d.msgOffset i ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset i + wd d i) := by
  intro g hg w hw hr
  have := hd.support_held t g hg w hw
  rw [held_toV_le hp hle hr] at this
  exact Bool.false_ne_true this

theorem slot_lt {k k' : ℕ} (hkk : k < k') {j : ℕ} (hj : wd d j ≤ hw d n k) : hPay d n k + wd d j ≤ hPay d n k' := by
  have h1 := hOff_mono d n (show k + 1 ≤ k' by omega)
  rw [hOff_succ] at h1
  unfold hPay
  split_ifs at h1 ⊢ <;> omega

/-- **The forward branch** of the honest prover is the honest run of `d`, displaced. -/
theorem gF_honest (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hsch : d.HasSchedule (2 * n + 1))
    (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (ιd : D → ℂ)
    (A : ∀ k, Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ)
    (hA : ∀ k (hk1 : 1 ≤ k) (hkn : k ≤ n), A k = honA d n D U k hk1 hkn)
    (ι : Bool × D → ℂ) (hξ : cutVec d n (A 0) ι = liftV d n false (dRun d D U ιd (n + 1)))
    (UF : Turns d ((Bool × D) × MB d n))
    (hUF : ∀ k, 1 ≤ k → k ≤ n → ∀ v, turnOp (UF (n + k)) *ᵥ v = tfOp d n (Bool × D) A k v) :
    ∀ j, j ≤ n → gF d n A ι UF j = liftV d n false (dRun d D U ιd (n + 1 + j)) ∘ dispF d n D j := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [gF, sufOp, one_mulVec, hξ]
    rfl
  | succ j ih =>
    intro hjn
    set k := j + 1 with hk
    have hk1 : 1 ≤ k := by omega
    have hkn : k ≤ n := hjn
    have hkm : n + k < 2 * n + 1 := by omega
    set L := liftV d n false (dRun d D U ιd (n + k)) with hL
    have hL' : liftV d n false (dRun d D U ιd (n + 1 + j)) = L := by
      rw [hL, show n + 1 + j = n + k by omega]
    rw [gF_succ, ih (by omega), hL', show n + 1 + j = n + k by omega, hUF k hk1 hkn]
    -- the state before the turn: coin copy `0`, copy wire `0`
    have hsupp : ∀ (π : Qubits d.totalWires × ((Bool × D) × MB d n) → Qubits d.totalWires × ((Bool × D) × MB d n)),
        (∀ z, (π z).2.1 = z.2.1) → (∀ z h, (π z).2.2 ⟨copyW d n, h⟩ = z.2.2 ⟨copyW d n, h⟩) →
        ∀ z, z.2.1.1 = true ∨ (∃ h : hPriv d ≤ ((copyW d n : Fin _) : ℕ), z.2.2 ⟨copyW d n, h⟩ = true) →
          (L ∘ π) z = 0 := by
      intro π h1 h2 z hz
      simp only [Function.comp_apply]
      apply liftV_vanish
      rcases hz with hz | ⟨h, hz⟩
      · left; rw [h1]; simp [hz]
      · right; exact ⟨⟨copyW d n, h⟩, by rw [h2]; exact hz⟩
    have hd1 : ∀ z, (dispF d n D j z).2.1 = z.2.1 := disp_mem _ _ j
    have hd2 : ∀ z h, (dispF d n D j z).2.2 ⟨copyW d n, h⟩ = z.2.2 ⟨copyW d n, h⟩ :=
      fun z h => disp_snd _ _ j z _ (copy_not_dispS hn _ _ j)
    have hσ2 : ∀ z h, (swL (D := D) (d := d) (n := n) k (n + k) z).2.2 ⟨copyW d n, h⟩ = z.2.2 ⟨copyW d n, h⟩ :=
      fun z h => σSw_snd_of z _ (fun h' => by have := copyW_lt_hPay (d := d) hn hk1; simp only at h'; omega)
    have hinv := σSw_involutive (N₀ := Bool × D) (d := d) (n := n)
      (show d.msgOffset (n + k) + wd d (n + k) ≤ d.totalWires from msgOffset_add_width_le d _)
      (hPay_ge k) (hPay_add_le hk1 hkn (wd_le_hw_fwd hk1))
    -- displaced registers are not register `n + k`
    have hdisW : ∀ k', 1 ≤ k' → k' ≤ j → k' % 2 = 1 → ∀ w : Fin d.totalWires, d.msgOffset (n + k') ≤ (w : ℕ) →
        (w : ℕ) < d.msgOffset (n + k') + wd d (n + k') → ¬ inReg d (n + k) w :=
      fun k' _ h2 _ w hw1 hw2 => region_not_inReg (by omega) hw1 hw2
    have hT : tfOp d n (Bool × D) A k (L ∘ dispF d n D j) = hon d n (n + k) (U (n + k)) L ∘ dispF d n D k := by
      simp only [tfOp, ifOp]
      rw [hA k hk1 hkn, honA]
      by_cases hodd : k % 2 = 1
      · rw [if_neg (by omega), if_pos hodd, id, proverOp_mul, proverOp_cpy]
        have hw : (swOp d n (Bool × D) k (n + k) (L ∘ dispF d n D j)) ∘ cpyL d n D k =
            L ∘ dispF d n D j ∘ swL k (n + k) :=
          comp_cpyL k _ (hsupp _ (fun z => (hd1 _).trans (σSw_mem z)) (fun z h => (hd2 _ h).trans (hσ2 z h)))
        rw [hw, proverOp_ctl hk1 hkn _ _ (U (n + k)) ((U (n + 1 - k))ᴴ) false
          (L ∘ dispF d n D j ∘ swL k (n + k)) (fun z hz => hsupp (dispF d n D j ∘ swL k (n + k))
          (fun z => (hd1 _).trans (σSw_mem z)) (fun z h => (hd2 _ h).trans (hσ2 z h)) z
          (Or.inl (by revert hz; cases z.2.1.1 <;> simp)))]
        simp only [Bool.false_eq_true, if_false]
        rw [show (L ∘ dispF d n D j ∘ swL k (n + k)) ∘ swL k (n + k) = L ∘ dispF d n D j by
          funext z; simp only [Function.comp_apply, hinv z],
          hon_disp _ _ (U (n + k)) j hdisW]
        show _ = hon d n (n + k) (U (n + k)) L ∘ disp d n D (fun k => n + k) (fun k => k % 2 = 1) (j + 1)
        simp only [disp, if_pos (show (j + 1) % 2 = 1 by omega)]
        rfl
      · have hev : k % 2 = 0 := by omega
        rw [if_pos hev, if_neg hodd, id, proverOp_mul, proverOp_cpy,
          comp_cpyL k _ (hsupp _ hd1 hd2)]
        rw [proverOp_ctl hk1 hkn _ _ (U (n + k)) ((U (n + 1 - k))ᴴ) false (L ∘ dispF d n D j)
          (fun z hz => hsupp (dispF d n D j) hd1 hd2 z (Or.inl (by revert hz; cases z.2.1.1 <;> simp)))]
        simp only [Bool.false_eq_true, if_false]
        have hzero : (L ∘ dispF d n D j) ∘ swL k (n + k) = L ∘ dispF d n D j := by
          refine comp_sw_of_zero hk1 hkn (wd_le_hw_fwd hk1) _ (fun z hz => ?_)
          simp only [Function.comp_apply]
          rcases hz with ⟨w, hw1, hw2, hw⟩ | ⟨u, hu1, hu2, hu⟩
          · have hnd : ¬ DispW d (fun k => n + k) (fun k => k % 2 = 1) j w :=
              fun ⟨k', h1, h2, _, h4, h5⟩ => region_not_inReg (show n + k' ≠ n + k by omega) h4 h5 ⟨hw1, hw2⟩
            simp only [hL, liftV]
            split_ifs
            · exact dRun_future hd U ιd (show ¬ toProverAt d (n + k) by
                rw [toP_iff_odd hsch hkm]; omega) ⟨hw1, hw2⟩ (n + k) le_rfl _ _
                (by rw [disp_fst _ _ j z w hnd]; exact hw)
            · rfl
          · have hnd : ¬ DispS d n (fun k => n + k) (fun k => k % 2 = 1) j u.1 := by
              rintro ⟨k', h1, h2, _, h4, h5⟩
              have := slot_lt (d := d) (show k' < k by omega) (wd_le_hw_fwd (n := n) (d := d) h1)
              simp only at h4 h5
              omega
            apply liftV_vanish
            right
            exact ⟨u, by rw [disp_snd _ _ j z u hnd]; exact hu⟩
        rw [show ∀ v, swOp d n (Bool × D) k (n + k) v = v ∘ swL k (n + k) from fun v => rfl,
          show ((hon d n (n + k) (U (n + k)) ((L ∘ dispF d n D j) ∘ swL k (n + k))) ∘ swL k (n + k)) ∘
          swL k (n + k) = hon d n (n + k) (U (n + k)) ((L ∘ dispF d n D j) ∘ swL k (n + k)) by
            funext z; simp only [Function.comp_apply, hinv z], hzero, hon_disp _ _ (U (n + k)) j hdisW]
        show _ = hon d n (n + k) (U (n + k)) L ∘ disp d n D (fun k => n + k) (fun k => k % 2 = 1) (j + 1)
        simp only [disp, if_neg (show ¬ (j + 1) % 2 = 1 by omega)]
    have hB : ∀ k', 1 ≤ k' → k' ≤ k → k' % 2 = 1 → ∀ g ∈ dI d (n + k + 1), ∀ w ∈ g.support,
        ¬ (d.msgOffset (n + k') ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset (n + k') + wd d (n + k')) :=
      fun k' h1 h2 h3 => dI_avoid_dead hd ((toP_iff_odd hsch (by omega)).mpr (by omega)) (by omega)
    rw [hT, bOp_disp _ _ k hB, hL, hon_liftV, bOp_liftV, show n + 1 + (j + 1) = n + k + 1 by omega, dRun]

end Forward


/-! ## Inverse blocks and displacement -/

section InvBlocks

variable {d : Desc} {n : ℕ} {N₀ : Type} [Fintype N₀] [DecidableEq N₀]

theorem layer_σSw {p q r : ℕ} (l : List (Instr d.totalWires))
    (hl : ∀ g ∈ l, ∀ w ∈ g.support, ¬ (q ≤ (w : ℕ) ∧ (w : ℕ) < q + r))
    (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) :
    (layerMat l ⊗ₖ (1 : Matrix (N₀ × MB d n) (N₀ × MB d n) ℂ)) *ᵥ (v ∘ σSw d n p q r) =
      ((layerMat l ⊗ₖ (1 : Matrix (N₀ × MB d n) (N₀ × MB d n) ℂ)) *ᵥ v) ∘ σSw d n p q r := by
  funext ⟨x, ν⟩
  simp only [Function.comp_apply]
  rw [kronOne_mulVec_apply, show σSw d n p q r (x, ν) = ((σSw d n p q r (x, ν)).1, (σSw d n p q r (x, ν)).2) from rfl,
    kronOne_mulVec_apply, layerMat_mulVec, layerMat_mulVec]
  have := runLayer_comp_fam (fun w : Fin d.totalWires => q ≤ (w : ℕ) ∧ (w : ℕ) < q + r)
    (fun x' => (σSw d n p q r (x', ν)).1)
    (fun y i b hi => by
      funext w
      simp only [σSw, Function.update_apply]
      by_cases hw : w = i
      · subst hw; rw [dif_neg (fun h => hi ⟨h.1, h.2.1⟩)]; simp
      · simp only [if_neg hw])
    (fun y i hi => σSw_fst_of (y, ν) i hi) l hl
    (fun x' => fun x'' => v (x'', (σSw d n p q r (x', ν)).2))
    (fun y i b hi => by
      funext x''
      congr 2
      simp only [σSw, Prod.mk.injEq, true_and]
      funext u
      split_ifs with h
      · rw [Function.update_of_ne]
        intro e; apply hi; rw [← e]; simp only; omega
      · rfl)
  exact congrFun this x

omit [Fintype N₀] in
theorem blockOpH_eq (j : ℕ) : (blockOp d (N₀ × MB d n) j)ᴴ =
    layerMat (adjointInstrs (dI d j)) ⊗ₖ (1 : Matrix (N₀ × MB d n) (N₀ × MB d n) ℂ) := by
  rw [blockOp, conjTranspose_kronecker, conjTranspose_one, layerMat_adjointInstrs]
  rfl

theorem bOpH_σSw {j p q r : ℕ} (hl : ∀ g ∈ dI d j, ∀ w ∈ g.support, ¬ (q ≤ (w : ℕ) ∧ (w : ℕ) < q + r))
    (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) :
    bOpH d n N₀ j (v ∘ σSw d n p q r) = bOpH d n N₀ j v ∘ σSw d n p q r := by
  simp only [bOpH, blockOpH_eq]
  refine layer_σSw _ (fun g hg w hw => ?_) v
  simp only [adjointInstrs, List.mem_flatten, List.mem_map, List.mem_reverse] at hg
  obtain ⟨l, ⟨g₀, hg₀, rfl⟩, hgl⟩ := hg
  exact hl g₀ hg₀ w (by rw [← support_instrInv hgl]; exact hw)

end InvBlocks

section DispH

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]
variable (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]

/-- **Inverse blocks commute with displacement** of registers they do not touch. -/
theorem bOpH_disp {t : ℕ} : ∀ j, (∀ k, 1 ≤ k → k ≤ j → P k → ∀ g ∈ dI d t, ∀ w ∈ g.support,
      ¬ (d.msgOffset (f k) ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset (f k) + wd d (f k))) →
    ∀ L : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ,
      bOpH d n (Bool × D) t (L ∘ disp d n D f P j) = bOpH d n (Bool × D) t L ∘ disp d n D f P j
  | 0, _, L => rfl
  | k + 1, h, L => by
    simp only [disp]
    split_ifs with hP
    · rw [← Function.comp_assoc, bOpH_σSw (h (k + 1) (by omega) le_rfl hP),
        bOpH_disp k (fun k' h1 h2 h3 => h k' h1 (by omega) h3), Function.comp_assoc]
    · exact bOpH_disp k (fun k' h1 h2 h3 => h k' h1 (by omega) h3) L

end DispH

/-! ## Facts on the honest run of `d` -/

section DRun2

variable {d : Desc} {D : Type} [Fintype D] [DecidableEq D]

theorem kron_blockMat_mem (j : ℕ) :
    blockMat d j ⊗ₖ (1 : Matrix D D ℂ) ∈ Matrix.unitaryGroup (Qubits d.totalWires × D) ℂ :=
  kronecker_mem_unitary (blockMat_mem_unitaryGroup d j) (one_mem _)

/-- Undoing block `t + 1` of the honest run gives the state after turn `t`. -/
theorem dRun_undo (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (ι : D → ℂ) (t : ℕ) :
    (blockMat d (t + 1) ⊗ₖ (1 : Matrix D D ℂ))ᴴ *ᵥ dRun d D U ι (t + 1) = tv t (U t) (dRun d D U ι t) := by
  rw [dRun, mulVec_mulVec, ← star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp (kron_blockMat_mem (D := D) (t + 1)), one_mulVec]

omit [DecidableEq D] in
theorem tv_mul_apply {t : ℕ} (A B : Matrix (Reg d t × D) (Reg d t × D) ℂ) (ψ : Qubits d.totalWires × D → ℂ) :
    tv t A (tv t B ψ) = tv t (A * B) ψ := (tv_mul t A B ψ).symm

theorem tv_one' {t : ℕ} (ψ : Qubits d.totalWires × D → ℂ) : tv t (1 : Matrix (Reg d t × D) (Reg d t × D) ℂ) ψ = ψ := by
  simp only [tv, one_kronecker_one, one_mulVec]
  funext p; simp

theorem tv_inv {t : ℕ} {A : Matrix (Reg d t × D) (Reg d t × D) ℂ} (hA : A ∈ Matrix.unitaryGroup _ ℂ)
    (ψ : Qubits d.totalWires × D → ℂ) : tv t Aᴴ (tv t A ψ) = ψ := by
  rw [tv_mul_apply, ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hA, tv_one']

end DRun2


/-! ## The coin copy in the backward branch -/

section CopyB

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

theorem copyW_inReg_iff (hn : 1 ≤ n) {k : ℕ} (hk : k ≤ n) : inReg (halveDesc d n) k (copyW d n) ↔ k = 1 := by
  rw [inReg_halve_iff hk, copyW_val hn]
  constructor
  · intro ⟨h1, h2⟩
    by_contra hk1
    rcases Nat.lt_or_gt_of_ne hk1 with h | h
    · obtain rfl : k = 0 := by omega
      have := hOff_succ d n 0
      simp [hw] at this h2
      omega
    · have h3 := hOff_mono d n (show 2 ≤ k by omega)
      have h4 : hOff d n 2 = hOff d n 1 + (hw d n 1 + 1) := by simpa using hOff_succ d n 1
      omega
  · rintro rfl; simp

omit [Fintype D] [DecidableEq D] in
theorem cpyL_of_ne {k : ℕ} (hc : ¬ inReg (halveDesc d n) k (copyW d n)) : cpyL d n D k = id := by
  funext z; simp only [cpyL, dif_neg hc, id]

omit [Fintype D] [DecidableEq D] in
/-- The coin copy, flipped by the verifier and moved into memory by the prover. -/
theorem liftV_flip_cpy (hn : 1 ≤ n) (ψ : Qubits d.totalWires × D → ℂ) :
    liftV d n false ψ ∘ flipZ d n (Bool × D) ∘ cpyL d n D 1 = liftV d n true ψ := by
  have hc : inReg (halveDesc d n) 1 (copyW d n) := (copyW_inReg_iff hn hn).mpr rfl
  funext ⟨x, ⟨c, μ⟩, β⟩
  simp only [Function.comp_apply, cpyL, dif_pos hc, flipZ, liftV]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    have hcw := h2 ⟨copyW d n, hPriv_le_of_inReg hc⟩
    simp only [if_true] at hcw
    refine ⟨by simpa using hcw, fun u => ?_⟩
    by_cases hu : u.1 = copyW d n
    · rw [show u = ⟨copyW d n, hPriv_le_of_inReg hc⟩ from Subtype.ext hu]; exact h1
    · have := h2 u; rwa [if_neg hu, if_neg hu] at this
  · rintro ⟨rfl, h2⟩
    refine ⟨h2 _, fun u => ?_⟩
    split_ifs with hu
    · simp
    · exact h2 u

omit [Fintype D] [DecidableEq D] in
theorem swL_cpyL (hn : 1 ≤ n) {k j : ℕ} (hk : 1 ≤ k) (z : Qubits d.totalWires × ((Bool × D) × MB d n)) :
    cpyL d n D 1 (swL k j z) = swL k j (cpyL d n D 1 z) := by
  have hlt := copyW_lt_hPay (d := d) hn hk
  by_cases hc : inReg (halveDesc d n) 1 (copyW d n)
  · obtain ⟨x, ⟨c, μ⟩, β⟩ := z
    simp only [cpyL, dif_pos hc, σSw]
    refine Prod.ext (funext fun w => ?_) (Prod.ext (Prod.ext ?_ rfl) (funext fun u => ?_))
    · simp only
      split_ifs with h h'
      · exfalso; have := congrArg Fin.val h'; simp only at this; omega
      · rfl
      · rfl
    · simp only
      split_ifs with h
      · exfalso; omega
      · rfl
    · simp only
      split_ifs with h1 h2 h3 <;> first
        | rfl
        | (exfalso; rw [h1] at h2; omega)
  · simp only [cpyL, dif_neg hc]

end CopyB


/-! ## The backward branch of the honest prover -/

section Backward

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

/-- Backward displacement: the messages `n + 1 - k` to the verifier (`k` odd) sit in the slots. -/
abbrev dispB (d : Desc) (n : ℕ) (D : Type) [Fintype D] [DecidableEq D] (j : ℕ) :=
  disp d n D (fun k => n + 1 - k) (fun k => k % 2 = 1) j

/-- **The backward branch** of the honest prover undoes the honest run of `d`, displaced. -/
theorem gB_honest (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hsch : d.HasSchedule (2 * n + 1))
    (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup _ ℂ) (ιd : D → ℂ)
    (hclean : ∀ i, toProverAt d i → ∀ (x : Qubits d.totalWires) μ (w : Fin d.totalWires), inReg d i w →
      x w = true → tv i (U i) (dRun d D U ιd i) (x, μ) = 0)
    (A : ∀ k, Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ)
    (hA : ∀ k (hk1 : 1 ≤ k) (hkn : k ≤ n), A k = honA d n D U k hk1 hkn)
    (ι : Bool × D → ℂ) (hξ : cutVec d n (A 0) ι = liftV d n false (dRun d D U ιd (n + 1)))
    (UB : Turns d ((Bool × D) × MB d n))
    (hUB : ∀ k, 1 ≤ k → k ≤ n → ∀ v, (turnOp (UB (n + 1 - k)))ᴴ *ᵥ v = tbOp d n (Bool × D) A k v) :
    ∀ j, 1 ≤ j → j ≤ n → gB d n A ι UB j = liftV d n true (dRun d D U ιd (n + 1 - j)) ∘ dispB d n D j := by
  intro j hj1
  induction j, hj1 using Nat.le_induction with
  | base =>
    intro _
    have h0 : gB d n A ι UB 0 = liftV d n false (dRun d D U ιd (n + 1)) := by
      simp only [gB, sufOp, conjTranspose_one, one_mulVec, hξ]
    have := gB_succ A ι UB (j := 0) (by omega)
    have h1 := hUB 1 le_rfl hn
    rw [show n + 1 - 1 = n by omega] at h1
    rw [h0, Nat.sub_zero, Nat.sub_zero, h1] at this
    rw [this, show n + 1 - 1 = n by omega, bOpH_liftV, dRun_undo]
    simp only [tbOp, ifOp, if_neg (show ¬ 1 % 2 = 0 by omega), id, if_true]
    rw [hA 1 le_rfl hn, honA, proverOp_mul, proverOp_cpy]
    have hlt := copyW_lt_hPay (d := d) hn (k := 1) le_rfl
    have hcomm : swOp d n (Bool × D) 1 (n + 1 - 1) (flipOp d n (Bool × D) (liftV d n false (tv n (U n)
        (dRun d D U ιd n)))) ∘ cpyL d n D 1 = liftV d n true (tv n (U n) (dRun d D U ιd n)) ∘ swL 1 (n + 1 - 1) := by
      rw [← liftV_flip_cpy hn]
      funext z
      simp only [swOp, flipOp, Function.comp_apply]
      rw [swL_cpyL hn le_rfl]
    rw [hcomm, proverOp_ctl le_rfl hn _ _ (U (n + 1)) ((U (n + 1 - 1))ᴴ) true
      (liftV d n true (tv n (U n) (dRun d D U ιd n)) ∘ swL 1 (n + 1 - 1))
      (fun z hz => by simp only [Function.comp_apply]; exact liftV_vanish (Or.inl (by rw [σSw_mem]; exact hz)))]
    simp only [if_true]
    have hinv := σSw_involutive (N₀ := Bool × D) (d := d) (n := n)
      (show d.msgOffset (n + 1 - 1) + wd d (n + 1 - 1) ≤ d.totalWires from msgOffset_add_width_le d _)
      (hPay_ge 1) (hPay_add_le le_rfl hn (wd_le_hw_bwd le_rfl))
    rw [show (liftV d n true (tv n (U n) (dRun d D U ιd n)) ∘ swL 1 (n + 1 - 1)) ∘ swL 1 (n + 1 - 1) =
      liftV d n true (tv n (U n) (dRun d D U ιd n)) by funext z; simp only [Function.comp_apply, hinv z],
      show n + 1 - 1 = n by omega, hon_liftV, tv_inv (hU n)]
    show _ = liftV d n true (dRun d D U ιd n) ∘ disp d n D (fun k => n + 1 - k) (fun k => k % 2 = 1) 1
    simp only [disp, show n + 1 - 1 = n by omega]
    rfl
  | succ j hj1 ih =>
    intro hjn
    set k := j + 1 with hk
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hkn : k ≤ n := hjn
    set t := n + 1 - k with ht
    have htn : t = n - j := by omega
    -- the state after undoing block `n + 1 - j`
    have hstep := gB_succ A ι UB (j := j) (by omega)
    rw [ih (by omega), show n - j = t by omega, hUB k hk1 hkn] at hstep
    rw [hstep]
    have hBl : ∀ k', 1 ≤ k' → k' ≤ j → k' % 2 = 1 → ∀ g ∈ dI d (n + 1 - j), ∀ w ∈ g.support,
        ¬ (d.msgOffset (n + 1 - k') ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset (n + 1 - k') + wd d (n + 1 - k')) :=
      fun k' h1 h2 h3 => dI_avoid_future hd (fun hp => by
        rw [toP_iff_odd hsch (by omega)] at hp; omega) (by omega)
    rw [bOpH_disp _ _ j hBl, bOpH_liftV, show n + 1 - j = t + 1 by omega, dRun_undo]
    set L := liftV d n true (tv t (U t) (dRun d D U ιd t)) with hL
    have hcpy : cpyL d n D k = id :=
      cpyL_of_ne (fun h => by rw [copyW_inReg_iff hn hkn] at h; omega)
    have hd1 : ∀ z, (dispB d n D j z).2.1 = z.2.1 := disp_mem _ _ j
    have hinv := σSw_involutive (N₀ := Bool × D) (d := d) (n := n)
      (show d.msgOffset t + wd d t ≤ d.totalWires from msgOffset_add_width_le d _)
      (hPay_ge k) (hPay_add_le hk1 hkn (by rw [ht]; exact wd_le_hw_bwd hk1))
    have hinv' : ∀ z, swL (D := D) (d := d) (n := n) k (n + 1 - k) (swL k (n + 1 - k) z) = z := hinv
    have hdisW : ∀ k', 1 ≤ k' → k' ≤ j → k' % 2 = 1 → ∀ w : Fin d.totalWires, d.msgOffset (n + 1 - k') ≤ (w : ℕ) →
        (w : ℕ) < d.msgOffset (n + 1 - k') + wd d (n + 1 - k') → ¬ inReg d t w :=
      fun k' _ h2 _ w hw1 hw2 => region_not_inReg (by omega) hw1 hw2
    have hsup : ∀ z, z.2.1.1 ≠ true → (L ∘ dispB d n D j) z = 0 := fun z hz => by
      simp only [Function.comp_apply]
      exact liftV_vanish (Or.inl (by rw [hd1]; exact hz))
    simp only [tbOp, ifOp, if_neg (show k ≠ 1 by omega), id]
    rw [hA k hk1 hkn, honA, proverOp_mul, proverOp_cpy, hcpy, Function.comp_id]
    by_cases hodd : k % 2 = 1
    · rw [if_neg (by omega), if_pos hodd, id]
      rw [proverOp_ctl hk1 hkn _ _ (U (n + k)) ((U (n + 1 - k))ᴴ) true
        (swOp d n (Bool × D) k (n + 1 - k) (L ∘ dispB d n D j))
        (fun z hz => hsup _ (by rw [σSw_mem]; exact hz))]
      simp only [if_true]
      rw [show swOp d n (Bool × D) k (n + 1 - k) (L ∘ dispB d n D j) ∘ swL k (n + 1 - k) = L ∘ dispB d n D j by
          funext z; simp only [swOp, Function.comp_apply, hinv' z],
        hon_disp _ _ ((U (n + 1 - k))ᴴ) j hdisW, hL, hon_liftV, tv_inv (hU t)]
      show _ = liftV d n true (dRun d D U ιd (n + 1 - (j + 1))) ∘
        disp d n D (fun k => n + 1 - k) (fun k => k % 2 = 1) (j + 1)
      simp only [disp, if_pos (show (j + 1) % 2 = 1 by omega)]
      rfl
    · have hev : k % 2 = 0 := by omega
      rw [if_pos hev, if_neg hodd, id]
      rw [proverOp_ctl hk1 hkn _ _ (U (n + k)) ((U (n + 1 - k))ᴴ) true (L ∘ dispB d n D j) hsup]
      simp only [if_true]
      have hzero : (L ∘ dispB d n D j) ∘ swL k (n + 1 - k) = L ∘ dispB d n D j := by
        refine comp_sw_of_zero hk1 hkn (wd_le_hw_bwd hk1) _ (fun z hz => ?_)
        simp only [Function.comp_apply]
        rcases hz with ⟨w, hw1, hw2, hw⟩ | ⟨u, hu1, hu2, hu⟩
        · have hnd : ¬ DispW d (fun k => n + 1 - k) (fun k => k % 2 = 1) j w :=
            fun ⟨k', h1, h2, _, h4, h5⟩ => region_not_inReg (show n + 1 - k' ≠ n + 1 - k by omega) h4 h5
              ⟨hw1, hw2⟩
          simp only [hL, liftV]
          split_ifs
          · exact hclean t ((toP_iff_odd hsch (by omega)).mpr (by omega)) _ _ w ⟨hw1, hw2⟩
              (by rw [disp_fst _ _ j z w hnd]; exact hw)
          · rfl
        · have hnd : ¬ DispS d n (fun k => n + 1 - k) (fun k => k % 2 = 1) j u.1 := by
            rintro ⟨k', h1, h2, _, h4, h5⟩
            have := slot_lt (d := d) (show k' < k by omega) (wd_le_hw_bwd (n := n) (d := d) h1)
            simp only at h4 h5
            omega
          apply liftV_vanish
          right
          exact ⟨u, by rw [disp_snd _ _ j z u hnd]; exact hu⟩
      rw [show ∀ v, swOp d n (Bool × D) k (n + 1 - k) v = v ∘ swL k (n + 1 - k) from fun v => rfl,
        show ((hon d n (n + 1 - k) (U (n + 1 - k))ᴴ ((L ∘ dispB d n D j) ∘ swL k (n + 1 - k))) ∘ swL k (n + 1 - k)) ∘
          swL k (n + 1 - k) = hon d n (n + 1 - k) (U (n + 1 - k))ᴴ ((L ∘ dispB d n D j) ∘ swL k (n + 1 - k)) by
            funext z; simp only [Function.comp_apply, hinv' z], hzero,
        hon_disp _ _ ((U (n + 1 - k))ᴴ) j hdisW, hL, hon_liftV, tv_inv (hU t)]
      show _ = liftV d n true (dRun d D U ιd (n + 1 - (j + 1))) ∘
        disp d n D (fun k => n + 1 - k) (fun k => k % 2 = 1) (j + 1)
      simp only [disp, if_neg (show ¬ (j + 1) % 2 = 1 by omega)]
      rfl

end Backward


/-! ## Accounting -/

section Account

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem sum_liftV (c : Bool) (ψ : Qubits d.totalWires × D → ℂ) (g : Qubits d.totalWires → ℝ) :
    ∑ z : Qubits d.totalWires × ((Bool × D) × MB d n), g z.1 * ‖liftV d n c ψ z‖ ^ 2 =
      ∑ x, ∑ μ, g x * ‖ψ (x, μ)‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool]
  have hz : ∀ c' μ, (∑ β : MB d n, g x * ‖liftV d n c ψ (x, ((c', μ), β))‖ ^ 2) =
      if c' = c then g x * ‖ψ (x, μ)‖ ^ 2 else 0 := by
    intro c' μ
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp only [liftV]
      split_ifs with h1 h2 h2 <;> simp_all
    · intro β _ hβ
      have : ¬ ∀ u, β u = false := fun h => hβ (funext h)
      simp only [liftV]
      rw [if_neg (fun h => this h.2)]
      simp
    · simp
  simp only [hz]
  cases c <;> simp

omit [DecidableEq D] in
/-- A weight on `d`-wires outside the displaced registers is displacement-invariant. -/
theorem sum_disp_wires (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (j : ℕ)
    (hb : ∀ k, 1 ≤ k → k ≤ j → P k → k ≤ n ∧ wd d (f k) ≤ hw d n k)
    (Q : Qubits d.totalWires → Prop) [DecidablePred Q]
    (hQ : ∀ k, 1 ≤ k → k ≤ j → P k → ∀ x x' : Qubits d.totalWires,
      (∀ w : Fin d.totalWires, ¬ (d.msgOffset (f k) ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset (f k) + wd d (f k)) →
        x' w = x w) → (Q x' ↔ Q x))
    (L : Qubits d.totalWires × ((Bool × D) × MB d n) → ℂ) :
    ∑ z, (if Q z.1 then (1 : ℝ) else 0) * ‖(L ∘ disp d n D f P j) z‖ ^ 2 =
      ∑ z, (if Q z.1 then (1 : ℝ) else 0) * ‖L z‖ ^ 2 := by
  refine sum_disp f P j hb _ (fun k h1 h2 h3 z => ?_) L
  rw [if_congr (hQ k h1 h2 h3 z.1 (swL k (f k) z).1 (fun w hw => σSw_fst_of z w hw)) rfl rfl]

/-- A layer avoiding register `t` commutes with a turn on register `t`. -/
theorem kron_tv {t : ℕ} (l : List (Instr d.totalWires)) (hl : ∀ g ∈ l, ∀ w ∈ g.support, ¬ inReg d t w)
    (A : Matrix (Reg d t × D) (Reg d t × D) ℂ) (v : Qubits d.totalWires × D → ℂ) :
    (layerMat l ⊗ₖ (1 : Matrix D D ℂ)) *ᵥ tv t A v = tv t A ((layerMat l ⊗ₖ (1 : Matrix D D ℂ)) *ᵥ v) := by
  funext ⟨y, μ'⟩
  rw [kronOne_mulVec_apply, tv_apply, layerMat_mulVec]
  have hfun : (fun y' => tv t A v (y', μ')) = ∑ s : Reg d t, ∑ μ : D, fun y' =>
      A ((wireSplitE d t y').2, μ') (s, μ) * v (PrefixData.regSet d t y' s, μ) := by
    funext y'; rw [tv_apply]; simp [Finset.sum_apply]
  rw [hfun, ← layerMat_mulVec, mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [layerMat_mulVec, kronOne_mulVec_apply, layerMat_mulVec]
  have := runLayer_comp (n := d.totalWires) (inReg d t) (fun y' => PrefixData.regSet d t y' s)
    (fun y i b hi => by
      funext w; simp only [PrefixData.regSet_apply, Function.update_apply]
      split_ifs with h1 h2 <;> first | rfl | (subst h2; exact absurd h1 hi))
    (fun y i hi => by simp only [PrefixData.regSet_apply, dif_neg hi])
    (fun y' => A ((wireSplitE d t y').2, μ') (s, μ))
    (fun y i b hi => by
      congr 2
      funext w
      simp only [wireSplitE, Equiv.trans_apply, Equiv.piEquivPiSubtypeProd_apply, Equiv.prodComm_apply,
        Prod.snd_swap, Function.update_apply]
      rw [if_neg]; intro e; rw [← e] at hi; exact hi w.2)
    l hl (fun y' => v (y', μ))
  exact congrFun this y

theorem nsq_tv {t : ℕ} {A : Matrix (Reg d t × D) (Reg d t × D) ℂ} (hA : A ∈ Matrix.unitaryGroup _ ℂ)
    (v : Qubits d.totalWires × D → ℂ) : nsq (tv t A v) = nsq v := by
  have hU : ((1 : Matrix (Rest d t) (Rest d t) ℂ) ⊗ₖ A) ∈ Matrix.unitaryGroup _ ℂ :=
    kronecker_mem_unitary (one_mem _) hA
  have h1 := nsq_unitary hU (v ∘ (turnSplit d t D).symm)
  have e : ∀ w : Qubits d.totalWires × D → ℂ, nsq (w ∘ (turnSplit d t D).symm) = nsq w := fun w =>
    Equiv.sum_comp (turnSplit d t D).symm (fun p => ‖w p‖ ^ 2)
  rw [e] at h1
  rw [← h1, tv]
  exact Equiv.sum_comp (turnSplit d t D) (fun p => ‖(((1 : Matrix (Rest d t) (Rest d t) ℂ) ⊗ₖ A) *ᵥ
    (v ∘ (turnSplit d t D).symm)) p‖ ^ 2)

end Account


/-! ## The honest prover succeeds in both branches -/

section Succeed

variable {d : Desc} {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]

theorem sum_ite_eq_mul {X : Type} [Fintype X] (Q : X → Prop) [DecidablePred Q] (f : X → ℝ) :
    (∑ x, if Q x then f x else 0) = ∑ x, (if Q x then (1 : ℝ) else 0) * f x :=
  Finset.sum_congr rfl fun x _ => by split_ifs <;> simp

theorem out_not_region (hd : d.Valid) (i : ℕ) : ¬ (d.msgOffset i ≤ d.out ∧ d.out < d.msgOffset i + wd d i) := by
  have h1 := hd.out_lt
  have h2 : d.priv ≤ d.msgOffset i := by simp [Desc.msgOffset]
  omega

theorem outBit_congr (hd : d.Valid) (i : ℕ) (x x' : Qubits d.totalWires)
    (h : ∀ w : Fin d.totalWires, ¬ (d.msgOffset i ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset i + wd d i) → x' w = x w) :
    outBit d x' ↔ outBit d x := by
  constructor
  · rintro ⟨hlt, hx⟩; exact ⟨hlt, by rw [← h _ (out_not_region hd i)]; exact hx⟩
  · rintro ⟨hlt, hx⟩; exact ⟨hlt, by rw [h _ (out_not_region hd i)]; exact hx⟩

/-- **The forward branch accepts as the honest prover of `d` does.** -/
theorem fwdP_honest (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hsch : d.HasSchedule (2 * n + 1))
    (hm : d.numMsgs = 2 * n + 1)
    (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (ιd : D → ℂ)
    (A : ∀ k, Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ)
    (hA : ∀ k (hk1 : 1 ≤ k) (hkn : k ≤ n), A k = honA d n D U k hk1 hkn)
    (ι : Bool × D → ℂ) (hξ : cutVec d n (A 0) ι = liftV d n false (dRun d D U ιd (n + 1)))
    (UF : Turns d ((Bool × D) × MB d n))
    (hUF : ∀ k, 1 ≤ k → k ≤ n → ∀ v, turnOp (UF (n + k)) *ᵥ v = tfOp d n (Bool × D) A k v) :
    fwdP UF (n + 1) (cutVec d n (A 0) ι) =
      ∑ x, ∑ μ, if outBit d x then ‖dRun d D U ιd (2 * n + 1) (x, μ)‖ ^ 2 else 0 := by
  have hg := gF_honest hd hn hne hsch U ιd A hA ι hξ UF hUF n le_rfl
  rw [fwdP, hm, show 2 * n + 1 - (n + 1) = n by omega, nsq_projQ,
    show sufOp UF (n + 1) n *ᵥ cutVec d n (A 0) ι = gF d n A ι UF n from rfl, hg,
    show n + 1 + n = 2 * n + 1 by omega]
  simp only [sum_ite_eq_mul]
  rw [← Fintype.sum_prod_type' (f := fun x ν => (if outBit d x then (1 : ℝ) else 0) *
    ‖(liftV d n false (dRun d D U ιd (2 * n + 1)) ∘ dispF d n D n) (x, ν)‖ ^ 2)]
  rw [sum_disp_wires (fun k => n + k) (fun k => k % 2 = 1) n
    (fun k h1 h2 _ => ⟨h2, wd_le_hw_fwd h1⟩) (outBit d)
    (fun k _ _ _ x x' h => outBit_congr hd (n + k) x x' h),
    sum_liftV false _ (fun x => if outBit d x then (1 : ℝ) else 0)]

theorem zero0_congr (hsch : d.HasSchedule (2 * n + 1)) {i : ℕ} (hi : i < 2 * n + 1) (he : i % 2 = 0)
    (x x' : Qubits d.totalWires)
    (h : ∀ w : Fin d.totalWires, ¬ (d.msgOffset i ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset i + wd d i) → x' w = x w) :
    Zero0 d x' ↔ Zero0 d x := by
  have hp : ¬ toProverAt d i := by rw [toP_iff_odd hsch hi]; omega
  have hh : ∀ w : Fin d.totalWires, d.held 0 w = true →
      ¬ (d.msgOffset i ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset i + wd d i) := fun w hw hr => by
    rw [held_toV_le hp (Nat.zero_le i) hr] at hw; exact Bool.false_ne_true hw
  constructor
  · intro h0 w hw; rw [← h w (hh w hw)]; exact h0 w hw
  · intro h0 w hw; rw [h w (hh w hw)]; exact h0 w hw

/-- **The backward branch returns to `|0⟩` with certainty.** -/
theorem bwdP_honest (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hsch : d.HasSchedule (2 * n + 1))
    (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup _ ℂ) (ιd : D → ℂ)
    (hιd : ∑ μ, ‖ιd μ‖ ^ 2 = 1)
    (hclean : ∀ i, toProverAt d i → ∀ (x : Qubits d.totalWires) μ (w : Fin d.totalWires), inReg d i w →
      x w = true → tv i (U i) (dRun d D U ιd i) (x, μ) = 0)
    (A : ∀ k, Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ)
    (hA : ∀ k (hk1 : 1 ≤ k) (hkn : k ≤ n), A k = honA d n D U k hk1 hkn)
    (ι : Bool × D → ℂ) (hξ : cutVec d n (A 0) ι = liftV d n false (dRun d D U ιd (n + 1)))
    (UB : Turns d ((Bool × D) × MB d n))
    (hUB : ∀ k, 1 ≤ k → k ≤ n → ∀ v, (turnOp (UB (n + 1 - k)))ᴴ *ᵥ v = tbOp d n (Bool × D) A k v)
    (hUB0 : ∀ v, (turnOp (UB 0))ᴴ *ᵥ v = v) :
    bwdP UB (n + 1) (cutVec d n (A 0) ι) = 1 := by
  have hg := gB_honest hd hn hne hsch U hU ιd hclean A hA ι hξ UB hUB n hn le_rfl
  have h1 := gB_succ A ι UB (j := n) le_rfl
  rw [Nat.sub_self, hUB0, show n + 1 - n = 1 by omega, hg, show n + 1 - n = 1 by omega] at h1
  have hBl : ∀ b, b ≤ 1 → ∀ k', 1 ≤ k' → k' ≤ n → k' % 2 = 1 → ∀ g ∈ dI d b, ∀ w ∈ g.support,
      ¬ (d.msgOffset (n + 1 - k') ≤ (w : ℕ) ∧ (w : ℕ) < d.msgOffset (n + 1 - k') + wd d (n + 1 - k')) :=
    fun b hb k' h1 h2 h3 => dI_avoid_future hd (fun hp => by
      rw [toP_iff_odd hsch (by omega)] at hp; omega) (by omega)
  rw [bwdP, preOp_adj_halve, h1, bOpH_disp _ _ n (hBl 1 le_rfl), bOpH_liftV, bOpH_disp _ _ n (hBl 0 (by omega)),
    bOpH_liftV, show (1 : ℕ) = 0 + 1 from rfl, dRun_undo, nsq_projQ]
  simp only [sum_ite_eq_mul]
  rw [← Fintype.sum_prod_type' (f := fun x ν => (if Zero0 d x then (1 : ℝ) else 0) * ‖(liftV d n true
    ((blockMat d 0 ⊗ₖ (1 : Matrix D D ℂ))ᴴ *ᵥ tv 0 (U 0) (dRun d D U ιd 0)) ∘ dispB d n D n) (x, ν)‖ ^ 2)]
  rw [sum_disp_wires (fun k => n + 1 - k) (fun k => k % 2 = 1) n
    (fun k h1 h2 _ => ⟨h2, wd_le_hw_bwd h1⟩) (Zero0 d)
    (fun k h1 h2 h3 x x' h => zero0_congr hsch (by omega) (by omega) x x' h),
    sum_liftV true _ (fun x => if Zero0 d x then (1 : ℝ) else 0)]
  -- turn `0` commutes with block `0`
  have hp0 : ¬ toProverAt d 0 := by rw [toP_iff_odd hsch (by omega)]; omega
  have hl0 : ∀ g ∈ dI d 0, ∀ w ∈ g.support, ¬ inReg d 0 w := fun g hg w hw hr => by
    have := hd.support_held 0 g hg w hw
    rw [held_toV_le hp0 le_rfl hr] at this; exact Bool.false_ne_true this
  set e : Qubits d.totalWires × D → ℂ := fun p => zeroVec d.totalWires p.1 * ιd p.2 with he
  have hφ : (blockMat d 0 ⊗ₖ (1 : Matrix D D ℂ))ᴴ *ᵥ tv 0 (U 0) (dRun d D U ιd 0) = tv 0 (U 0) e := by
    rw [dRun, show blockMat d 0 = layerMat (dI d 0) from rfl, ← kron_tv _ hl0, mulVec_mulVec,
      ← star_eq_conjTranspose]
    rw [show layerMat (dI d 0) = blockMat d 0 from rfl,
      Matrix.mem_unitaryGroup_iff'.mp (kron_blockMat_mem (D := D) 0), one_mulVec]
  rw [hφ]
  -- the zero test passes on the support
  have hsupp : ∀ x μ, ¬ Zero0 d x → tv 0 (U 0) e (x, μ) = 0 := by
    intro x μ hx
    simp only [Zero0, not_forall] at hx
    obtain ⟨w, hw0, hxw⟩ := hx
    have hw : ¬ inReg d 0 w := fun hr => by
      rw [held_toV_le hp0 le_rfl hr] at hw0; exact Bool.false_ne_true hw0
    refine tv_vanish _ hw e (fun x' μ' hx' => ?_) x μ (by simpa using hxw)
    simp only [he, zeroVec]
    rw [if_neg (fun h => by rw [h] at hx'; exact Bool.false_ne_true hx'), zero_mul]
  have h2 : (∑ x, ∑ μ, (if Zero0 d x then (1 : ℝ) else 0) * ‖tv 0 (U 0) e (x, μ)‖ ^ 2) = nsq (tv 0 (U 0) e) := by
    rw [nsq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    split_ifs with h
    · rw [one_mul]
    · rw [hsupp x μ h]; simp
  rw [h2, nsq_tv (hU 0), nsq, Fintype.sum_prod_type, Finset.sum_eq_single (Qubits.zero d.totalWires)]
  · simpa [he, zeroVec] using hιd
  · intro x _ hx; simp [he, zeroVec, hx]
  · simp

end Succeed

end ShiQIP
