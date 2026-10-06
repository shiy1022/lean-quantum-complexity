/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Pair.Interleave
import QIP.TesterProduct
import QIP.Circuit.Relabel

/-!
# Q25 — the paired verifier description

`pairDesc d₁ d₂` runs two verifier descriptions with the same message schedule side by side.

* **Wires.** Wire `0` is a fresh ancilla, which is also the output wire. Then come the private
  registers of `d₁` and of `d₂`. Then, for each message `j`, the register of `d₁`'s message `j`
  followed by that of `d₂`'s. The layout is that of the segment lists
  `a = priv₁ :: widths₁` and `b = priv₂ :: widths₂` interleaved (`QIP.Pair.Interleave`), shifted
  by one. Copy-1 wire `x` goes to `pos₁ x`, copy-2 wire `y` to `pos₂ y`.
* **Messages.** Message `j` has direction `dir₁ j` and width `width₁ j + width₂ j`.
* **Blocks.** Block `j` runs the relabelled block `j` of `d₁`, then that of `d₂`. The last block
  then ends with a Toffoli from the two output wires into the ancilla, which computes the
  all-pass bit.

This file sets up the layout: the wire maps, their injectivity and disjointness, and how they
correspond to message registers and held wires.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow

/-! ## Message lists -/

/-- The paired message list. -/
def pairMsgs (ms₁ ms₂ : List Message) : List Message :=
  List.zipWith (fun m₁ m₂ => ⟨m₁.dir, m₁.width + m₂.width⟩) ms₁ ms₂

theorem pairMsgs_widths : ∀ (ms₁ ms₂ : List Message),
    (pairMsgs ms₁ ms₂).map Message.width = zw (ms₁.map Message.width) (ms₂.map Message.width)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | m₁ :: ms₁, m₂ :: ms₂ => by
    simp only [pairMsgs, List.zipWith_cons_cons, List.map_cons, zw] at *
    rw [show List.zipWith (fun m₁ m₂ : Message => (⟨m₁.dir, m₁.width + m₂.width⟩ : Message)) ms₁ ms₂
      = pairMsgs ms₁ ms₂ from rfl, pairMsgs_widths ms₁ ms₂]
    rfl

theorem pairMsgs_dirs : ∀ (ms₁ ms₂ : List Message), ms₁.length = ms₂.length →
    (pairMsgs ms₁ ms₂).map Message.dir = ms₁.map Message.dir
  | [], [], _ => rfl
  | m₁ :: ms₁, m₂ :: ms₂, h => by
    simp only [pairMsgs, List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact pairMsgs_dirs ms₁ ms₂ (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem length_pairMsgs (ms₁ ms₂ : List Message) (h : ms₁.length = ms₂.length) :
    (pairMsgs ms₁ ms₂).length = ms₁.length := by
  simp [pairMsgs, List.length_zipWith, h]

/-! ## Segment lists of a description -/

/-- The segment widths of a description: private register, then the messages. -/
def segs (d : Desc) : List ℕ := d.priv :: d.msgs.map Message.width

theorem segs_sum (d : Desc) : (segs d).sum = d.totalWires := rfl

theorem segs_length (d : Desc) : (segs d).length = d.numMsgs + 1 := by
  simp [segs, Desc.numMsgs]

theorem msgWidth_eq (d : Desc) (j : ℕ) : d.msgWidth j = (segs d).getD (j + 1) 0 := by
  simp [Desc.msgWidth, segs, List.getD_eq_getElem?_getD, List.getElem?_map]

theorem msgOffset_eq (d : Desc) (j : ℕ) : d.msgOffset j = psum (segs d) (j + 1) := by
  simp [Desc.msgOffset, segs, psum, List.map_take]

/-- **Message registers are segments.** -/
theorem inReg_iff_segIdx (d : Desc) (j : ℕ) (x : Fin d.totalWires) :
    inReg d j x ↔ segIdx (segs d) x = j + 1 := by
  unfold inReg
  rw [msgOffset_eq, msgWidth_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact segIdx_eq h1 h2
  · intro h
    have := segIdx_spec (segs d) x (by rw [segs_sum]; exact x.2)
    rw [h] at this
    exact this

/-! ## The paired description -/

variable (d₁ d₂ : Desc)

/-- Position of copy-1 wire `x`. -/
def pos₁ (x : ℕ) : ℕ :=
  1 + psum (zw (segs d₁) (segs d₂)) (segIdx (segs d₁) x) + (x - psum (segs d₁) (segIdx (segs d₁) x))

/-- Position of copy-2 wire `y`. -/
def pos₂ (y : ℕ) : ℕ :=
  1 + psum (zw (segs d₁) (segs d₂)) (segIdx (segs d₂) y) + (segs d₁).getD (segIdx (segs d₂) y) 0 +
    (y - psum (segs d₂) (segIdx (segs d₂) y))

/-- One block of the paired description. -/
def pairBlock (j : ℕ) : List Gate :=
  (d₁.blocks.getD j []).map (Gate.relabel (pos₁ d₁ d₂)) ++
    (d₂.blocks.getD j []).map (Gate.relabel (pos₂ d₁ d₂)) ++
      (if j = d₁.numMsgs then toffoliGates (pos₁ d₁ d₂ d₁.out) (pos₂ d₁ d₂ d₂.out) 0 else [])

/-- **The paired description.** -/
def pairDesc : Desc where
  priv := 1 + d₁.priv + d₂.priv
  out := 0
  msgs := pairMsgs d₁.msgs d₂.msgs
  blocks := (List.range (d₁.numMsgs + 1)).map (pairBlock d₁ d₂)

variable {d₁ d₂}

theorem segs_pairDesc :
    segs (pairDesc d₁ d₂) = (d₁.priv + d₂.priv + 1) :: (zw (segs d₁) (segs d₂)).tail := by
  simp only [segs, pairDesc, pairMsgs_widths, zw, List.zipWith_cons_cons, List.tail_cons]
  congr 1; ring

theorem totalWires_pairDesc :
    (pairDesc d₁ d₂).totalWires = 1 + (zw (segs d₁) (segs d₂)).sum := by
  simp only [Desc.totalWires, pairDesc, pairMsgs_widths, zw, segs, List.zipWith_cons_cons,
    List.sum_cons]
  ring

theorem numMsgs_pairDesc (hlen : d₁.numMsgs = d₂.numMsgs) :
    (pairDesc d₁ d₂).numMsgs = d₁.numMsgs :=
  length_pairMsgs _ _ hlen

theorem segs_length_eq (hlen : d₁.numMsgs = d₂.numMsgs) :
    (segs d₁).length = (segs d₂).length := by
  rw [segs_length, segs_length, hlen]

/-! ## The wire maps -/

theorem pos₁_of_seg {x i : ℕ} (h1 : psum (segs d₁) i ≤ x) (h2 : x < psum (segs d₁) i + (segs d₁).getD i 0) :
    pos₁ d₁ d₂ x = 1 + psum (zw (segs d₁) (segs d₂)) i + (x - psum (segs d₁) i) := by
  rw [pos₁, segIdx_eq h1 h2]

theorem pos₂_of_seg {y i : ℕ} (h1 : psum (segs d₂) i ≤ y) (h2 : y < psum (segs d₂) i + (segs d₂).getD i 0) :
    pos₂ d₁ d₂ y = 1 + psum (zw (segs d₁) (segs d₂)) i + (segs d₁).getD i 0 + (y - psum (segs d₂) i) := by
  rw [pos₂, segIdx_eq h1 h2]

theorem pos₁_lt (hlen : d₁.numMsgs = d₂.numMsgs) {x : ℕ} (hx : x < d₁.totalWires) :
    pos₁ d₁ d₂ x < (pairDesc d₁ d₂).totalWires := by
  have hl := segs_length_eq hlen
  obtain ⟨s1, s2⟩ := segIdx_spec (segs d₁) x hx
  rw [pos₁_of_seg s1 s2, totalWires_pairDesc]
  have := psum_add_getD_le (zw (segs d₁) (segs d₂)) (segIdx (segs d₁) x)
  rw [getD_zw _ _ hl] at this
  omega

theorem pos₂_lt (hlen : d₁.numMsgs = d₂.numMsgs) {y : ℕ} (hy : y < d₂.totalWires) :
    pos₂ d₁ d₂ y < (pairDesc d₁ d₂).totalWires := by
  have hl := segs_length_eq hlen
  obtain ⟨s1, s2⟩ := segIdx_spec (segs d₂) y hy
  rw [pos₂_of_seg s1 s2, totalWires_pairDesc]
  have := psum_add_getD_le (zw (segs d₁) (segs d₂)) (segIdx (segs d₂) y)
  rw [getD_zw _ _ hl] at this
  omega

/-- The segment of a paired position. -/
theorem segIdx_pos₁ (hlen : d₁.numMsgs = d₂.numMsgs) {x : ℕ} (hx : x < d₁.totalWires) :
    segIdx (zw (segs d₁) (segs d₂)) (pos₁ d₁ d₂ x - 1) = segIdx (segs d₁) x := by
  have hl := segs_length_eq hlen
  obtain ⟨s1, s2⟩ := segIdx_spec (segs d₁) x hx
  rw [pos₁_of_seg s1 s2]
  apply segIdx_eq
  · omega
  · rw [getD_zw _ _ hl]; omega

theorem segIdx_pos₂ (hlen : d₁.numMsgs = d₂.numMsgs) {y : ℕ} (hy : y < d₂.totalWires) :
    segIdx (zw (segs d₁) (segs d₂)) (pos₂ d₁ d₂ y - 1) = segIdx (segs d₂) y := by
  have hl := segs_length_eq hlen
  obtain ⟨s1, s2⟩ := segIdx_spec (segs d₂) y hy
  rw [pos₂_of_seg s1 s2]
  apply segIdx_eq
  · omega
  · rw [getD_zw _ _ hl]; omega

theorem pos₁_pos (x : ℕ) : 0 < pos₁ d₁ d₂ x := by unfold pos₁; omega
theorem pos₂_pos (y : ℕ) : 0 < pos₂ d₁ d₂ y := by unfold pos₂; omega

theorem pos₁_inj (hlen : d₁.numMsgs = d₂.numMsgs) {x x' : ℕ} (hx : x < d₁.totalWires)
    (hx' : x' < d₁.totalWires) (h : pos₁ d₁ d₂ x = pos₁ d₁ d₂ x') : x = x' := by
  have hi := segIdx_pos₁ (d₂ := d₂) hlen hx
  have hi' := segIdx_pos₁ (d₂ := d₂) hlen hx'
  rw [h] at hi
  have he : segIdx (segs d₁) x = segIdx (segs d₁) x' := hi.symm.trans hi'
  obtain ⟨s1, s2⟩ := segIdx_spec (segs d₁) x hx
  obtain ⟨t1, t2⟩ := segIdx_spec (segs d₁) x' hx'
  unfold pos₁ at h
  rw [he] at h s1 s2
  omega

theorem pos₂_inj (hlen : d₁.numMsgs = d₂.numMsgs) {y y' : ℕ} (hy : y < d₂.totalWires)
    (hy' : y' < d₂.totalWires) (h : pos₂ d₁ d₂ y = pos₂ d₁ d₂ y') : y = y' := by
  have hi := segIdx_pos₂ (d₁ := d₁) hlen hy
  have hi' := segIdx_pos₂ (d₁ := d₁) hlen hy'
  rw [h] at hi
  have he : segIdx (segs d₂) y = segIdx (segs d₂) y' := hi.symm.trans hi'
  obtain ⟨s1, s2⟩ := segIdx_spec (segs d₂) y hy
  obtain ⟨t1, t2⟩ := segIdx_spec (segs d₂) y' hy'
  unfold pos₂ at h
  rw [he] at h s1 s2
  omega

theorem pos₁_ne_pos₂ (hlen : d₁.numMsgs = d₂.numMsgs) {x y : ℕ} (hx : x < d₁.totalWires)
    (hy : y < d₂.totalWires) : pos₁ d₁ d₂ x ≠ pos₂ d₁ d₂ y := by
  intro h
  have hi := segIdx_pos₁ (d₂ := d₂) hlen hx
  have hi' := segIdx_pos₂ (d₁ := d₁) hlen hy
  rw [h] at hi
  have he : segIdx (segs d₂) y = segIdx (segs d₁) x := hi'.symm.trans hi
  obtain ⟨s1, s2⟩ := segIdx_spec (segs d₁) x hx
  obtain ⟨t1, t2⟩ := segIdx_spec (segs d₂) y hy
  unfold pos₁ pos₂ at h
  rw [he] at h t1 t2
  omega

/-! ## Registers of the paired description -/

theorem segIdx_shift (h : ℕ) (rest : List ℕ) (v : ℕ) :
    segIdx ((h + 1) :: rest) (v + 1) = segIdx (h :: rest) v := by
  simp only [segIdx]
  by_cases hv : v < h
  · rw [if_pos (by omega), if_pos hv]
  · rw [if_neg (by omega), if_neg hv]
    congr 2; omega

theorem segIdx_pairDesc (v : ℕ) :
    segIdx (segs (pairDesc d₁ d₂)) (v + 1) = segIdx (zw (segs d₁) (segs d₂)) v := by
  rw [segs_pairDesc]
  have : zw (segs d₁) (segs d₂) = (d₁.priv + d₂.priv) :: (zw (segs d₁) (segs d₂)).tail := rfl
  rw [this, segIdx_shift]
  rfl

theorem inReg_pair_iff (v : Fin (pairDesc d₁ d₂).totalWires) (j : ℕ) (hv : 0 < (v : ℕ)) :
    inReg (pairDesc d₁ d₂) j v ↔ segIdx (zw (segs d₁) (segs d₂)) (v - 1) = j + 1 := by
  rw [inReg_iff_segIdx, ← segIdx_pairDesc, Nat.sub_add_cancel hv]

theorem not_inReg_pair_zero (j : ℕ) (h : 0 < (pairDesc d₁ d₂).totalWires) :
    ¬ inReg (pairDesc d₁ d₂) j ⟨0, h⟩ := by
  rw [inReg_iff_segIdx]
  simp [segs, pairDesc, segIdx]

variable (d₁ d₂) in
/-- The copy-1 embedding. -/
def emb₁ (hlen : d₁.numMsgs = d₂.numMsgs) : Fin d₁.totalWires ↪ Fin (pairDesc d₁ d₂).totalWires :=
  ⟨fun x => ⟨pos₁ d₁ d₂ x, pos₁_lt hlen x.2⟩, fun x x' h =>
    Fin.ext (pos₁_inj hlen x.2 x'.2 (congrArg Fin.val h))⟩

variable (d₁ d₂) in
/-- The copy-2 embedding. -/
def emb₂ (hlen : d₁.numMsgs = d₂.numMsgs) : Fin d₂.totalWires ↪ Fin (pairDesc d₁ d₂).totalWires :=
  ⟨fun y => ⟨pos₂ d₁ d₂ y, pos₂_lt hlen y.2⟩, fun y y' h =>
    Fin.ext (pos₂_inj hlen y.2 y'.2 (congrArg Fin.val h))⟩

theorem inReg_emb₁ (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ) (x : Fin d₁.totalWires) :
    inReg (pairDesc d₁ d₂) j (emb₁ d₁ d₂ hlen x) ↔ inReg d₁ j x := by
  rw [inReg_pair_iff _ _ (pos₁_pos (x : ℕ)), inReg_iff_segIdx]
  change segIdx _ (pos₁ d₁ d₂ x - 1) = _ ↔ _
  rw [segIdx_pos₁ hlen x.2]

theorem inReg_emb₂ (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ) (y : Fin d₂.totalWires) :
    inReg (pairDesc d₁ d₂) j (emb₂ d₁ d₂ hlen y) ↔ inReg d₂ j y := by
  rw [inReg_pair_iff _ _ (pos₂_pos (y : ℕ)), inReg_iff_segIdx]
  change segIdx _ (pos₂ d₁ d₂ y - 1) = _ ↔ _
  rw [segIdx_pos₂ hlen y.2]

variable (d₁ d₂) in
/-- Both copies together. -/
def embSum (hlen : d₁.numMsgs = d₂.numMsgs) :
    Fin d₁.totalWires ⊕ Fin d₂.totalWires ↪ Fin (pairDesc d₁ d₂).totalWires :=
  ⟨Sum.elim (emb₁ d₁ d₂ hlen) (emb₂ d₁ d₂ hlen), by
    rintro (x | y) (x' | y') h
    · exact congrArg Sum.inl ((emb₁ d₁ d₂ hlen).injective h)
    · exact absurd (congrArg Fin.val h) (pos₁_ne_pos₂ hlen x.2 y'.2)
    · exact absurd (congrArg Fin.val h).symm (pos₁_ne_pos₂ hlen x'.2 y.2)
    · exact congrArg Sum.inr ((emb₂ d₁ d₂ hlen).injective h)⟩

theorem totalWires_pair_eq (hlen : d₁.numMsgs = d₂.numMsgs) :
    (pairDesc d₁ d₂).totalWires = 1 + (d₁.totalWires + d₂.totalWires) := by
  rw [totalWires_pairDesc, sum_zw _ _ (segs_length_eq hlen), segs_sum, segs_sum]

variable (d₁ d₂) in
/-- The ancilla wire. -/
def ancWire (hlen : d₁.numMsgs = d₂.numMsgs) : Fin (pairDesc d₁ d₂).totalWires :=
  ⟨0, by rw [totalWires_pair_eq hlen]; omega⟩

theorem ancWire_notMem (hlen : d₁.numMsgs = d₂.numMsgs) :
    ancWire d₁ d₂ hlen ∉ Set.range (embSum d₁ d₂ hlen) := by
  rintro ⟨s, hs⟩
  have := congrArg Fin.val hs
  rcases s with x | y
  · exact absurd this (pos₁_pos (x : ℕ)).ne'
  · exact absurd this (pos₂_pos (y : ℕ)).ne'

/-- **Every wire is a copy wire or the ancilla** (by counting). -/
theorem eq_ancWire_of_notMem (hlen : d₁.numMsgs = d₂.numMsgs) (v : Fin (pairDesc d₁ d₂).totalWires)
    (hv : v ∉ Set.range (embSum d₁ d₂ hlen)) : v = ancWire d₁ d₂ hlen := by
  by_contra hne
  have hcard : Fintype.card (Outside (embSum d₁ d₂ hlen)) = 1 := by
    rw [Fintype.card_subtype_compl, Set.card_range_of_injective (embSum d₁ d₂ hlen).injective]
    simp [totalWires_pair_eq hlen]
  obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.mp hcard
  have e1 := hc ⟨v, hv⟩
  have e2 := hc ⟨ancWire d₁ d₂ hlen, ancWire_notMem hlen⟩
  exact hne (congrArg Subtype.val (e1.trans e2.symm))

instance outsideUnique (hlen : d₁.numMsgs = d₂.numMsgs) : Unique (Outside (embSum d₁ d₂ hlen)) where
  default := ⟨ancWire d₁ d₂ hlen, ancWire_notMem hlen⟩
  uniq r := Subtype.ext (eq_ancWire_of_notMem hlen r.1 r.2)

variable (d₁ d₂) in
/-- **The wire bijection of the paired description.** -/
noncomputable def pairSigma (hlen : d₁.numMsgs = d₂.numMsgs) :
    Qubits (pairDesc d₁ d₂).totalWires ≃ (Qubits d₁.totalWires × Qubits d₂.totalWires) × Bool :=
  letI := outsideUnique hlen
  (embSplit (embSum d₁ d₂ hlen)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).prodCongr (Equiv.funUnique _ Bool))

theorem pairSigma_apply (hlen : d₁.numMsgs = d₂.numMsgs) (w : Qubits (pairDesc d₁ d₂).totalWires) :
    pairSigma d₁ d₂ hlen w =
      ((fun x => w (emb₁ d₁ d₂ hlen x), fun y => w (emb₂ d₁ d₂ hlen y)), w (ancWire d₁ d₂ hlen)) :=
  rfl

/-! ## Register bijections -/

theorem ancWire_not_inReg (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ) :
    ¬ inReg (pairDesc d₁ d₂) j (ancWire d₁ d₂ hlen) :=
  not_inReg_pair_zero j _

theorem mem_range_of_inReg (hlen : d₁.numMsgs = d₂.numMsgs) {j : ℕ}
    {v : Fin (pairDesc d₁ d₂).totalWires} (hv : inReg (pairDesc d₁ d₂) j v) :
    v ∈ Set.range (embSum d₁ d₂ hlen) := by
  by_contra h
  exact ancWire_not_inReg hlen j (eq_ancWire_of_notMem hlen v h ▸ hv)

variable (d₁ d₂) in
/-- The register map on positions. -/
def regMap (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ) :
    {x // inReg d₁ j x} ⊕ {y // inReg d₂ j y} → {v // inReg (pairDesc d₁ d₂) j v}
  | .inl x => ⟨emb₁ d₁ d₂ hlen x.1, (inReg_emb₁ hlen j x.1).mpr x.2⟩
  | .inr y => ⟨emb₂ d₁ d₂ hlen y.1, (inReg_emb₂ hlen j y.1).mpr y.2⟩

theorem regMap_bijective (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ) :
    Function.Bijective (regMap d₁ d₂ hlen j) := by
  constructor
  · rintro (x | y) (x' | y') h <;> simp only [regMap, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext ((emb₁ d₁ d₂ hlen).injective h))
    · exact absurd (congrArg Fin.val h) (pos₁_ne_pos₂ hlen x.1.2 y'.1.2)
    · exact absurd (congrArg Fin.val h).symm (pos₁_ne_pos₂ hlen x'.1.2 y.1.2)
    · exact congrArg Sum.inr (Subtype.ext ((emb₂ d₁ d₂ hlen).injective h))
  · rintro ⟨v, hv⟩
    obtain ⟨s, rfl⟩ := mem_range_of_inReg hlen hv
    rcases s with x | y
    · exact ⟨.inl ⟨x, (inReg_emb₁ hlen j x).mp hv⟩, rfl⟩
    · exact ⟨.inr ⟨y, (inReg_emb₂ hlen j y).mp hv⟩, rfl⟩

variable (d₁ d₂) in
/-- **The register bijection** `Reg (pairDesc d₁ d₂) j ≃ Reg d₁ j × Reg d₂ j`. -/
noncomputable def pairTau (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ) :
    Reg (pairDesc d₁ d₂) j ≃ Reg d₁ j × Reg d₂ j :=
  (Equiv.arrowCongr (Equiv.ofBijective _ (regMap_bijective hlen j)).symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem pairTau_apply (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ) (r : Reg (pairDesc d₁ d₂) j) :
    pairTau d₁ d₂ hlen j r =
      (fun x : {x // inReg d₁ j x} => r ⟨emb₁ d₁ d₂ hlen x.1, (inReg_emb₁ hlen j x.1).mpr x.2⟩,
        fun y : {y // inReg d₂ j y} => r ⟨emb₂ d₁ d₂ hlen y.1, (inReg_emb₂ hlen j y.1).mpr y.2⟩) := by
  rfl

theorem wireSplitE_snd (d : Desc) (j : ℕ) (w : Qubits d.totalWires) :
    (wireSplitE d j w).2 = fun r => w r.1 := rfl

theorem wireSplitE_symm_apply (d : Desc) (j : ℕ) (a : Rest d j) (b : Reg d j)
    (v : Fin d.totalWires) :
    (wireSplitE d j).symm (a, b) v = if h : inReg d j v then b ⟨v, h⟩ else a ⟨v, h⟩ := rfl

theorem wireSplitE_fst_apply (d : Desc) (j : ℕ) (w : Qubits d.totalWires) (r : {v // ¬ inReg d j v}) :
    (wireSplitE d j w).1 r = w r.1 := rfl

theorem pair_reg_read (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ)
    (w : Qubits (pairDesc d₁ d₂).totalWires) :
    pairTau d₁ d₂ hlen j (wireSplitE (pairDesc d₁ d₂) j w).2 =
      ((wireSplitE d₁ j (pairSigma d₁ d₂ hlen w).1.1).2,
        (wireSplitE d₂ j (pairSigma d₁ d₂ hlen w).1.2).2) := by
  rw [pairTau_apply]
  rfl

theorem pair_reg_write (hlen : d₁.numMsgs = d₂.numMsgs) (j : ℕ)
    (w : Qubits (pairDesc d₁ d₂).totalWires) (X : Reg (pairDesc d₁ d₂) j) :
    pairSigma d₁ d₂ hlen ((wireSplitE (pairDesc d₁ d₂) j).symm
        ((wireSplitE (pairDesc d₁ d₂) j w).1, X)) =
      (((wireSplitE d₁ j).symm ((wireSplitE d₁ j (pairSigma d₁ d₂ hlen w).1.1).1,
          (pairTau d₁ d₂ hlen j X).1),
        (wireSplitE d₂ j).symm ((wireSplitE d₂ j (pairSigma d₁ d₂ hlen w).1.2).1,
          (pairTau d₁ d₂ hlen j X).2)), (pairSigma d₁ d₂ hlen w).2) := by
  rw [pairTau_apply]
  simp only [pairSigma_apply]
  refine Prod.ext (Prod.ext (funext fun x => ?_) (funext fun y => ?_)) ?_
  · simp only [wireSplitE_symm_apply]
    by_cases h : inReg d₁ j x
    · rw [dif_pos ((inReg_emb₁ hlen j x).mpr h), dif_pos h]
    · rw [dif_neg (fun h' => h ((inReg_emb₁ hlen j x).mp h')), dif_neg h]; rfl
  · simp only [wireSplitE_symm_apply]
    by_cases h : inReg d₂ j y
    · rw [dif_pos ((inReg_emb₂ hlen j y).mpr h), dif_pos h]
    · rw [dif_neg (fun h' => h ((inReg_emb₂ hlen j y).mp h')), dif_neg h]; rfl
  · simp only [wireSplitE_symm_apply]
    rw [dif_neg (ancWire_not_inReg hlen j)]
    rfl

theorem pairSigma_zero (hlen : d₁.numMsgs = d₂.numMsgs) :
    pairSigma d₁ d₂ hlen (Qubits.zero _) = ((Qubits.zero _, Qubits.zero _), false) := rfl

theorem pair_zero (hlen : d₁.numMsgs = d₂.numMsgs) (w : Qubits (pairDesc d₁ d₂).totalWires) :
    zeroVec (pairDesc d₁ d₂).totalWires w =
      zeroVec d₁.totalWires (pairSigma d₁ d₂ hlen w).1.1 *
        zeroVec d₂.totalWires (pairSigma d₁ d₂ hlen w).1.2 * ancZero (pairSigma d₁ d₂ hlen w).2 := by
  have key : w = Qubits.zero _ ↔ pairSigma d₁ d₂ hlen w = ((Qubits.zero _, Qubits.zero _), false) := by
    rw [← pairSigma_zero hlen, (pairSigma d₁ d₂ hlen).apply_eq_iff_eq]
  simp only [zeroVec]
  by_cases h : w = Qubits.zero _
  · have h' := key.mp h
    rw [if_pos h, h']
    simp [ancZero]
  · rw [if_neg h]
    have h' : ¬ pairSigma d₁ d₂ hlen w = ((Qubits.zero _, Qubits.zero _), false) := fun e => h (key.mpr e)
    generalize pairSigma d₁ d₂ hlen w = s at h' ⊢
    obtain ⟨⟨p, q⟩, b⟩ := s
    simp only [Prod.mk.injEq, not_and] at h'
    by_cases hp : p = Qubits.zero _ <;> by_cases hq : q = Qubits.zero _ <;> cases b <;>
      simp_all [ancZero]

/-! ## Blocks -/

open scoped Kronecker

theorem mem_range_emb (hlen : d₁.numMsgs = d₂.numMsgs) (r : Fin (pairDesc d₁ d₂).totalWires) :
    (∃ x, emb₁ d₁ d₂ hlen x = r) ∨ (∃ y, emb₂ d₁ d₂ hlen y = r) ∨ r = ancWire d₁ d₂ hlen := by
  by_cases h : r ∈ Set.range (embSum d₁ d₂ hlen)
  · obtain ⟨s, rfl⟩ := h
    rcases s with x | y
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr (Or.inl ⟨y, rfl⟩)
  · exact Or.inr (Or.inr (eq_ancWire_of_notMem hlen r h))

theorem emb₁_ne_emb₂ (hlen : d₁.numMsgs = d₂.numMsgs) (x : Fin d₁.totalWires)
    (y : Fin d₂.totalWires) : emb₁ d₁ d₂ hlen x ≠ emb₂ d₁ d₂ hlen y :=
  fun h => pos₁_ne_pos₂ hlen x.2 y.2 (congrArg Fin.val h)

theorem emb₁_ne_anc (hlen : d₁.numMsgs = d₂.numMsgs) (x : Fin d₁.totalWires) :
    emb₁ d₁ d₂ hlen x ≠ ancWire d₁ d₂ hlen :=
  fun h => (pos₁_pos (x : ℕ)).ne' (congrArg Fin.val h)

theorem emb₂_ne_anc (hlen : d₁.numMsgs = d₂.numMsgs) (y : Fin d₂.totalWires) :
    emb₂ d₁ d₂ hlen y ≠ ancWire d₁ d₂ hlen :=
  fun h => (pos₂_pos (y : ℕ)).ne' (congrArg Fin.val h)

/-- A copy-1 circuit as a block of the paired description. -/
theorem kron_embSplit₁ (hlen : d₁.numMsgs = d₂.numMsgs)
    (A : Matrix (Qubits d₁.totalWires) (Qubits d₁.totalWires) ℂ) :
    (A ⊗ₖ (1 : Matrix (Outside (emb₁ d₁ d₂ hlen) → Bool) _ ℂ)).submatrix
        (embSplit (emb₁ d₁ d₂ hlen)) (embSplit (emb₁ d₁ d₂ hlen)) =
      blockTens (pairSigma d₁ d₂ hlen) A 1 := by
  ext w w'
  simp only [blockTens, submatrix_apply, kroneckerMap_apply, pairSigma_apply, one_apply]
  have key : (embSplit (emb₁ d₁ d₂ hlen) w).2 = (embSplit (emb₁ d₁ d₂ hlen) w').2 ↔
      ((fun y => w (emb₂ d₁ d₂ hlen y)) = fun y => w' (emb₂ d₁ d₂ hlen y)) ∧
        w (ancWire d₁ d₂ hlen) = w' (ancWire d₁ d₂ hlen) := by
    constructor
    · intro h
      refine ⟨funext fun y => ?_, ?_⟩
      · exact congrFun h ⟨emb₂ d₁ d₂ hlen y, fun ⟨x, hx⟩ => emb₁_ne_emb₂ hlen x y hx⟩
      · exact congrFun h ⟨ancWire d₁ d₂ hlen, fun ⟨x, hx⟩ => emb₁_ne_anc hlen x hx⟩
    · rintro ⟨h1, h2⟩
      funext r
      rcases mem_range_emb hlen r.1 with ⟨x, hx⟩ | ⟨y, hy⟩ | ha
      · exact absurd ⟨x, hx⟩ r.2
      · change w r.1 = w' r.1
        rw [← hy]; exact congrFun h1 y
      · change w r.1 = w' r.1
        rw [ha]; exact h2
  by_cases h : (embSplit (emb₁ d₁ d₂ hlen) w).2 = (embSplit (emb₁ d₁ d₂ hlen) w').2
  · obtain ⟨h1, h2⟩ := key.mp h
    rw [if_pos h, if_pos h1, if_pos h2]; simp only [mul_one]; rfl
  · rw [if_neg h]
    by_cases h1 : ((fun y => w (emb₂ d₁ d₂ hlen y)) = fun y => w' (emb₂ d₁ d₂ hlen y))
    · rw [if_pos h1, if_neg (fun h2 => h (key.mpr ⟨h1, h2⟩))]; simp
    · rw [if_neg h1]; simp

/-- A copy-2 circuit as a block of the paired description. -/
theorem kron_embSplit₂ (hlen : d₁.numMsgs = d₂.numMsgs)
    (A : Matrix (Qubits d₂.totalWires) (Qubits d₂.totalWires) ℂ) :
    (A ⊗ₖ (1 : Matrix (Outside (emb₂ d₁ d₂ hlen) → Bool) _ ℂ)).submatrix
        (embSplit (emb₂ d₁ d₂ hlen)) (embSplit (emb₂ d₁ d₂ hlen)) =
      blockTens (pairSigma d₁ d₂ hlen) 1 A := by
  ext w w'
  simp only [blockTens, submatrix_apply, kroneckerMap_apply, pairSigma_apply, one_apply]
  have key : (embSplit (emb₂ d₁ d₂ hlen) w).2 = (embSplit (emb₂ d₁ d₂ hlen) w').2 ↔
      ((fun x => w (emb₁ d₁ d₂ hlen x)) = fun x => w' (emb₁ d₁ d₂ hlen x)) ∧
        w (ancWire d₁ d₂ hlen) = w' (ancWire d₁ d₂ hlen) := by
    constructor
    · intro h
      refine ⟨funext fun x => ?_, ?_⟩
      · exact congrFun h ⟨emb₁ d₁ d₂ hlen x, fun ⟨y, hy⟩ => emb₁_ne_emb₂ hlen x y hy.symm⟩
      · exact congrFun h ⟨ancWire d₁ d₂ hlen, fun ⟨y, hy⟩ => emb₂_ne_anc hlen y hy⟩
    · rintro ⟨h1, h2⟩
      funext r
      rcases mem_range_emb hlen r.1 with ⟨x, hx⟩ | ⟨y, hy⟩ | ha
      · change w r.1 = w' r.1
        rw [← hx]; exact congrFun h1 x
      · exact absurd ⟨y, hy⟩ r.2
      · change w r.1 = w' r.1
        rw [ha]; exact h2
  by_cases h : (embSplit (emb₂ d₁ d₂ hlen) w).2 = (embSplit (emb₂ d₁ d₂ hlen) w').2
  · obtain ⟨h1, h2⟩ := key.mp h
    rw [if_pos h, if_pos h1, if_pos h2]; simp only [mul_one, one_mul]; rfl
  · rw [if_neg h]
    by_cases h1 : ((fun x => w (emb₁ d₁ d₂ hlen x)) = fun x => w' (emb₁ d₁ d₂ hlen x))
    · rw [if_pos h1, if_neg (fun h2 => h (key.mpr ⟨h1, h2⟩))]; simp
    · rw [if_neg h1]; simp

theorem blockTens_mul_blockTens {V V₁ V₂ : Type} [Fintype V] [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (σ : V ≃ (V₁ × V₂) × Bool) (A : Matrix V₁ V₁ ℂ)
    (B : Matrix V₂ V₂ ℂ) : blockTens σ 1 B * blockTens σ A 1 = blockTens σ A B := by
  rw [blockTens, blockTens, blockTens, submatrix_mul_equiv, ← mul_kronecker_mul,
    ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

/-- The translated gates of block `j` of a valid description. -/
theorem layerMat_relabel₁ (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid) (j : ℕ) :
    layerMat (((d₁.blocks.getD j []).map (Gate.relabel (pos₁ d₁ d₂))).filterMap
        (Gate.toInstr? (pairDesc d₁ d₂).totalWires)) =
      blockTens (pairSigma d₁ d₂ hlen) (blockMat d₁ j) 1 := by
  rw [filterMap_relabel (emb₁ d₁ d₂ hlen) (pos₁ d₁ d₂) (fun _ => rfl) _ (hd₁.toInstr?_isSome j),
    layerMat_map, kron_embSplit₁]
  rfl

theorem layerMat_relabel₂ (hlen : d₁.numMsgs = d₂.numMsgs) (hd₂ : d₂.Valid) (j : ℕ) :
    layerMat (((d₂.blocks.getD j []).map (Gate.relabel (pos₂ d₁ d₂))).filterMap
        (Gate.toInstr? (pairDesc d₁ d₂).totalWires)) =
      blockTens (pairSigma d₁ d₂ hlen) 1 (blockMat d₂ j) := by
  rw [filterMap_relabel (emb₂ d₁ d₂ hlen) (pos₂ d₁ d₂) (fun _ => rfl) _ (hd₂.toInstr?_isSome j),
    layerMat_map, kron_embSplit₂]
  rfl

theorem blocks_pairDesc_getD {j : ℕ} (hj : j ≤ d₁.numMsgs) :
    (pairDesc d₁ d₂).blocks.getD j [] = pairBlock d₁ d₂ j := by
  simp [pairDesc, List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hj]

/-- **Blocks before the last are tensor products.** -/
theorem pair_block_prod (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid) (hd₂ : d₂.Valid)
    {j : ℕ} (hj : j < d₁.numMsgs) :
    blockMat (pairDesc d₁ d₂) j =
      blockTens (pairSigma d₁ d₂ hlen) (blockMat d₁ j) (blockMat d₂ j) := by
  rw [blockMat, blocks_pairDesc_getD hj.le, pairBlock, if_neg hj.ne, List.append_nil,
    List.filterMap_append, layerMat_append, layerMat_relabel₁ hlen hd₁, layerMat_relabel₂ hlen hd₂,
    blockTens_mul_blockTens]

/-! ## The last block -/

theorem layerMat_toffoli_apply {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (y y' : Qubits n) :
    layerMat (toffoliInstrs a b c hab hac hbc) y y' =
      if Function.update y c (xor (y c) (y a && y b)) = y' then 1 else 0 := by
  have h := congrFun (layerMat_mulVec (toffoliInstrs a b c hab hac hbc) (Pi.single y' 1)) y
  rw [mulVec_single_one, runLayer_toffoli] at h
  change (layerMat (toffoliInstrs a b c hab hac hbc)).col y' y = _
  rw [h, Pi.single_apply]

/-- The Toffoli map is an involution. -/
theorem toffoliFun_involutive {n : ℕ} {a b c : Fin n} (hac : a ≠ c) (hbc : b ≠ c) (y : Qubits n) :
    Function.update (Function.update y c (xor (y c) (y a && y b))) c
        (xor (Function.update y c (xor (y c) (y a && y b)) c)
          (Function.update y c (xor (y c) (y a && y b)) a &&
            Function.update y c (xor (y c) (y a && y b)) b)) = y := by
  rw [Function.update_self, Function.update_of_ne hac, Function.update_of_ne hbc,
    Function.update_idem, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Function.update_eq_self]

/-- **The Toffoli conjugates the effect `p` to `p ∘ toffoli`.** -/
theorem toffoli_conj_basisEffect {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Qubits n → Prop) [DecidablePred p] (w w' : Qubits n) :
    ((layerMat (toffoliInstrs a b c hab hac hbc))ᴴ * basisEffect p *
        layerMat (toffoliInstrs a b c hab hac hbc)) w w' =
      if w = w' ∧ p (Function.update w c (xor (w c) (w a && w b))) then 1 else 0 := by
  have hinv := toffoliFun_involutive (b := b) hac hbc
  rw [basisEffect, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, layerMat_toffoli_apply]
  rw [Finset.sum_eq_single (Function.update w c (xor (w c) (w a && w b)))]
  · simp only [hinv]
    by_cases h1 : w = w' <;> by_cases h2 : p (Function.update w c (xor (w c) (w a && w b))) <;>
      simp [h1, h2]
  · intro v _ hv
    have : ¬ Function.update v c (xor (v c) (v a && v b)) = w := fun h => hv (by rw [← h, hinv])
    simp [this]
  · simp

variable (d₁) in
/-- The copy-1 output wire. -/
def outW₁ (hd₁ : d₁.Valid) : Fin d₁.totalWires := ⟨d₁.out, by
  have := hd₁.out_lt; unfold Desc.totalWires; omega⟩

variable (d₂) in
/-- The copy-2 output wire. -/
def outW₂ (hd₂ : d₂.Valid) : Fin d₂.totalWires := ⟨d₂.out, by
  have := hd₂.out_lt; unfold Desc.totalWires; omega⟩

variable (d₁ d₂) in
/-- The all-pass Toffoli of the paired description. -/
noncomputable def pairF (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid) (hd₂ : d₂.Valid) :
    Matrix (Qubits (pairDesc d₁ d₂).totalWires) (Qubits (pairDesc d₁ d₂).totalWires) ℂ :=
  layerMat (toffoliInstrs (emb₁ d₁ d₂ hlen (outW₁ d₁ hd₁)) (emb₂ d₁ d₂ hlen (outW₂ d₂ hd₂))
    (ancWire d₁ d₂ hlen) (emb₁_ne_emb₂ hlen _ _) (emb₁_ne_anc hlen _) (emb₂_ne_anc hlen _))

/-- **The last block**: the tensor product, then the all-pass Toffoli. -/
theorem pair_block_last (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid) (hd₂ : d₂.Valid) :
    blockMat (pairDesc d₁ d₂) (pairDesc d₁ d₂).numMsgs =
      pairF d₁ d₂ hlen hd₁ hd₂ * blockTens (pairSigma d₁ d₂ hlen)
        (blockMat d₁ (pairDesc d₁ d₂).numMsgs) (blockMat d₂ (pairDesc d₁ d₂).numMsgs) := by
  rw [numMsgs_pairDesc hlen, blockMat, blocks_pairDesc_getD le_rfl, pairBlock, if_pos rfl,
    List.filterMap_append, List.filterMap_append, layerMat_append, layerMat_append,
    layerMat_relabel₁ hlen hd₁, layerMat_relabel₂ hlen hd₂, blockTens_mul_blockTens]
  have ht := filterMap_toffoliGates (emb₁ d₁ d₂ hlen (outW₁ d₁ hd₁))
    (emb₂ d₁ d₂ hlen (outW₂ d₂ hd₂)) (ancWire d₁ d₂ hlen) (emb₁_ne_emb₂ hlen _ _)
    (emb₁_ne_anc hlen _) (emb₂_ne_anc hlen _)
  change (toffoliGates (pos₁ d₁ d₂ d₁.out) (pos₂ d₁ d₂ d₂.out) 0).filterMap _ = _ at ht
  rw [ht]
  rfl

/-- **The final effect**: on the clean ancilla, the Toffoli turns "ancilla = 1" into
"both outputs = 1". -/
theorem pair_final_effect (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid) (hd₂ : d₂.Valid)
    (w w' : Qubits (pairDesc d₁ d₂).totalWires) (hw : (pairSigma d₁ d₂ hlen w).2 = false)
    (hw' : (pairSigma d₁ d₂ hlen w').2 = false) :
    ((pairF d₁ d₂ hlen hd₁ hd₂)ᴴ * basisEffect (outBit (pairDesc d₁ d₂)) *
        pairF d₁ d₂ hlen hd₁ hd₂) w w' =
      basisEffect (outBit d₁) (pairSigma d₁ d₂ hlen w).1.1 (pairSigma d₁ d₂ hlen w').1.1 *
        basisEffect (outBit d₂) (pairSigma d₁ d₂ hlen w).1.2 (pairSigma d₁ d₂ hlen w').1.2 := by
  rw [pairF, toffoli_conj_basisEffect]
  simp only [pairSigma_apply] at hw hw' ⊢
  have hσ : w = w' ↔ ((fun x => w (emb₁ d₁ d₂ hlen x)) = fun x => w' (emb₁ d₁ d₂ hlen x)) ∧
      ((fun y => w (emb₂ d₁ d₂ hlen y)) = fun y => w' (emb₂ d₁ d₂ hlen y)) := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      have : pairSigma d₁ d₂ hlen w = pairSigma d₁ d₂ hlen w' := by
        rw [pairSigma_apply, pairSigma_apply, h1, h2, hw, hw']
      exact (pairSigma d₁ d₂ hlen).injective this
  have hout : outBit (pairDesc d₁ d₂) (Function.update w (ancWire d₁ d₂ hlen)
      (xor (w (ancWire d₁ d₂ hlen)) (w (emb₁ d₁ d₂ hlen (outW₁ d₁ hd₁)) &&
        w (emb₂ d₁ d₂ hlen (outW₂ d₂ hd₂))))) ↔
      (w (emb₁ d₁ d₂ hlen (outW₁ d₁ hd₁)) = true ∧
        w (emb₂ d₁ d₂ hlen (outW₂ d₂ hd₂)) = true) := by
    unfold outBit
    constructor
    · rintro ⟨h, h'⟩
      have e : (⟨(pairDesc d₁ d₂).out, h⟩ : Fin _) = ancWire d₁ d₂ hlen := rfl
      rw [e, Function.update_self, hw] at h'
      simpa using h'
    · rintro ⟨h1, h2⟩
      refine ⟨(ancWire d₁ d₂ hlen).2, ?_⟩
      have e : (⟨(pairDesc d₁ d₂).out, (ancWire d₁ d₂ hlen).2⟩ : Fin _) = ancWire d₁ d₂ hlen :=
        rfl
      rw [e, Function.update_self, hw, h1, h2]; rfl
  have ho₁ : ∀ p : Qubits d₁.totalWires, outBit d₁ p ↔ p (outW₁ d₁ hd₁) = true := fun p =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨(outW₁ d₁ hd₁).2, h⟩⟩
  have ho₂ : ∀ q : Qubits d₂.totalWires, outBit d₂ q ↔ q (outW₂ d₂ hd₂) = true := fun q =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨(outW₂ d₂ hd₂).2, h⟩⟩
  simp only [basisEffect, diagonal_apply]
  by_cases h1 : ((fun x => w (emb₁ d₁ d₂ hlen x)) = fun x => w' (emb₁ d₁ d₂ hlen x))
  · by_cases h2 : ((fun y => w (emb₂ d₁ d₂ hlen y)) = fun y => w' (emb₂ d₁ d₂ hlen y))
    · have hww : w = w' := hσ.mpr ⟨h1, h2⟩
      subst hww
      simp only [true_and, if_true, ho₁, ho₂, hout]
      by_cases a1 : w (emb₁ d₁ d₂ hlen (outW₁ d₁ hd₁)) = true <;>
        by_cases a2 : w (emb₂ d₁ d₂ hlen (outW₂ d₂ hd₂)) = true <;> simp [a1, a2]
    · have hww : ¬ w = w' := fun e => h2 (by rw [e])
      simp [hww, h2]
  · have hww : ¬ w = w' := fun e => h1 (by rw [e])
    simp [hww, h1]

/-! ## The product theorem for the paired description -/

variable (d₁ d₂) in
/-- **The parallel-composition data of the paired description.** -/
noncomputable def pairData (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid) (hd₂ : d₂.Valid) :
    PairData d₁ d₂ (pairDesc d₁ d₂) where
  σ := pairSigma d₁ d₂ hlen
  τ := pairTau d₁ d₂ hlen
  reg_read := pair_reg_read hlen
  reg_write := pair_reg_write hlen
  zero := pair_zero hlen
  block_prod j hj := pair_block_prod hlen hd₁ hd₂ (by rwa [numMsgs_pairDesc hlen] at hj)
  F := pairF d₁ d₂ hlen hd₁ hd₂
  block_last := pair_block_last hlen hd₁ hd₂
  final_effect := pair_final_effect hlen hd₁ hd₂

/-- **Q25 (binary)**: the all-pass parallel composition of two valid verifiers with the same
number of messages has game value `value d₁ * value d₂`, against arbitrary provers. -/
theorem value_pairDesc (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid) (hd₂ : d₂.Valid) :
    value (pairDesc d₁ d₂) = value d₁ * value d₂ :=
  (pairData d₁ d₂ hlen hd₁ hd₂).value_eq (numMsgs_pairDesc hlen).symm
    ((numMsgs_pairDesc hlen).trans hlen).symm

end ShiQIP
