/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Valid
import QIP.Arithmetic.Padding

/-!
# Q29 — message padding

`padDesc d s` puts `s` zero-width messages, with empty blocks, in front of `d`. Their directions
continue the standard schedule backwards, so `d.HasSchedule m` gives
`(padDesc d s).HasSchedule (m + s)` (**`hasSchedule_padDesc`**). Every wire, register and gate
of `d` is unchanged; only message and block indices move up by `s`.

* `padDesc_valid`: the padded description is valid.
* **`value_padDesc`**: the value is unchanged. A prover of `padDesc d s` is, after its first `s`
  turns (which see no qubit), a prover of `d` with a prepared initial memory
  (`shiftT`, `accept_shiftT`); conversely a prover of `d` waits `s` turns.
* `exists_accept_padDesc`: every acceptance probability of `d` is one of `padDesc d s`.
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Syntax -/

/-- The `s` dummy messages in front of an `m`-message schedule. -/
def dummyMsgs (m s : ℕ) : List Message := ((stdSchedule (m + s)).take s).map fun dir => ⟨dir, 0⟩

/-- **Padding by `s` zero-width messages in front.** -/
def padDesc (d : Desc) (s : ℕ) : Desc where
  priv := d.priv
  out := d.out
  msgs := dummyMsgs d.numMsgs s ++ d.msgs
  blocks := List.replicate s [] ++ d.blocks

variable {d : Desc} {s : ℕ}

theorem length_stdSchedule (k : ℕ) : (stdSchedule k).length = k := by simp [stdSchedule]

theorem length_dummyMsgs (m s : ℕ) : (dummyMsgs m s).length = s := by
  simp [dummyMsgs, length_stdSchedule]

theorem numMsgs_padDesc : (padDesc d s).numMsgs = s + d.numMsgs := by
  simp [padDesc, Desc.numMsgs, length_dummyMsgs]

theorem width_of_mem_dummyMsgs {m s : ℕ} {msg : Message} (h : msg ∈ dummyMsgs m s) :
    msg.width = 0 := by
  simp only [dummyMsgs, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

theorem width_dummyMsgs (m s : ℕ) : ((dummyMsgs m s).map Message.width).sum = 0 := by
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨msg, hmsg, rfl⟩ := List.mem_map.mp hx
  exact width_of_mem_dummyMsgs hmsg

theorem totalWires_padDesc : (padDesc d s).totalWires = d.totalWires := by
  simp [padDesc, Desc.totalWires, width_dummyMsgs]

theorem msgOffset_padDesc (j : ℕ) : (padDesc d s).msgOffset (s + j) = d.msgOffset j := by
  simp only [Desc.msgOffset, padDesc]
  rw [show s + j = (dummyMsgs d.numMsgs s).length + j by rw [length_dummyMsgs],
    List.take_length_add_append, List.map_append, List.sum_append, width_dummyMsgs, zero_add]

theorem msgWidth_padDesc (j : ℕ) : (padDesc d s).msgWidth (s + j) = d.msgWidth j := by
  simp only [Desc.msgWidth, padDesc]
  rw [List.getElem?_append_right (by simp [length_dummyMsgs])]
  simp [length_dummyMsgs]

theorem msgWidth_padDesc_lt {i : ℕ} (hi : i < s) : (padDesc d s).msgWidth i = 0 := by
  have hl : i < (dummyMsgs d.numMsgs s).length := by rw [length_dummyMsgs]; exact hi
  simp only [Desc.msgWidth, padDesc]
  rw [List.getElem?_append_left hl, List.getElem?_eq_getElem hl, Option.map_some, Option.getD_some]
  exact width_of_mem_dummyMsgs (List.getElem_mem hl)

theorem getElem_stdSchedule {k i : ℕ} (hi : i < (stdSchedule k).length) :
    (stdSchedule k)[i] = if (k - 1 - i) % 2 = 0 then Dir.toVerifier else Dir.toProver := by
  simp [stdSchedule]

theorem drop_stdSchedule (m s : ℕ) : (stdSchedule (m + s)).drop s = stdSchedule m := by
  refine List.ext_getElem (by simp [length_stdSchedule]) fun i h1 h2 => ?_
  rw [List.getElem_drop, getElem_stdSchedule, getElem_stdSchedule]
  rw [show m + s - 1 - (s + i) = m - 1 - i by omega]

theorem dirs_padDesc {m : ℕ} (hs : d.HasSchedule m) :
    (padDesc d s).msgs.map Message.dir = stdSchedule (m + s) := by
  have hm := Desc.numMsgs_of_hasSchedule hs
  unfold Desc.HasSchedule at hs
  simp only [padDesc, List.map_append, hs, dummyMsgs, List.map_map, hm]
  conv_rhs => rw [← List.take_append_drop s (stdSchedule (m + s)), drop_stdSchedule]
  congr 1
  simp [Function.comp_def]

theorem hasSchedule_padDesc {m : ℕ} (hs : d.HasSchedule m) : (padDesc d s).HasSchedule (m + s) :=
  dirs_padDesc hs

/-! ## Validity -/

theorem msgHeld_zero_prefix (J w : ℕ) :
    ∀ (l ms : List Message) (k off : ℕ), (∀ msg ∈ l, msg.width = 0) →
      msgHeld J w (l ++ ms) k off = msgHeld J w ms (k + l.length) off
  | [], ms, k, off, _ => rfl
  | a :: l, ms, k, off, h => by
    have ha := h a List.mem_cons_self
    rw [List.cons_append, msgHeld, ha, Nat.add_zero,
      msgHeld_zero_prefix J w l ms (k + 1) off fun msg hm => h msg (List.mem_cons_of_mem _ hm)]
    simp only [show ∀ x : ℕ, ¬ (off ≤ x ∧ x < off) from fun x h => by omega, decide_false,
      Bool.false_and, Bool.false_or, List.length_cons]
    rw [show k + 1 + l.length = k + (l.length + 1) by omega]

theorem msgHeld_shift (j w s : ℕ) :
    ∀ (ms : List Message) (k off : ℕ), msgHeld (s + j) w ms (k + s) off = msgHeld j w ms k off
  | [], _, _ => rfl
  | m :: ms, k, off => by
    rw [msgHeld, msgHeld, show k + s + 1 = (k + 1) + s by omega, msgHeld_shift j w s ms]
    cases m.dir <;> simp [Nat.add_comm s, Nat.add_lt_add_iff_right, Nat.add_le_add_iff_right]

theorem msgHeld_shift_zero (j w s : ℕ) (ms : List Message) (off : ℕ) :
    msgHeld (s + j) w ms s off = msgHeld j w ms 0 off := by
  have := msgHeld_shift j w s ms 0 off
  rwa [Nat.zero_add] at this

/-- **Held wires move with the blocks.** -/
theorem held_padDesc (j w : ℕ) : (padDesc d s).held (s + j) w = d.held j w := by
  simp only [Desc.held, padDesc]
  rw [msgHeld_zero_prefix _ _ _ _ _ _ fun _ hm => width_of_mem_dummyMsgs hm, length_dummyMsgs,
    Nat.zero_add, msgHeld_shift_zero]
  rfl

theorem blocks_padDesc_getD (j : ℕ) : (padDesc d s).blocks.getD (s + j) [] = d.blocks.getD j [] := by
  simp only [padDesc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem blocks_padDesc_getD_lt {i : ℕ} (hi : i < s) : (padDesc d s).blocks.getD i [] = [] := by
  simp only [padDesc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem stdSchedule_succ (k : ℕ) :
    stdSchedule (k + 1) = (if k % 2 = 0 then Dir.toVerifier else Dir.toProver) :: stdSchedule k := by
  refine List.ext_getElem (by simp [length_stdSchedule]) fun i h1 h2 => ?_
  rw [getElem_stdSchedule]
  cases i with
  | zero => simp
  | succ i =>
    rw [List.getElem_cons_succ, getElem_stdSchedule]
    rw [show k + 1 - 1 - (i + 1) = k - 1 - i by omega]

theorem alternates_canon : ∀ k : ℕ,
    Desc.alternates ((stdSchedule k).map fun dir => (⟨dir, 0⟩ : Message)) = true
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    have ih := alternates_canon (k + 1)
    rw [stdSchedule_succ k, List.map_cons] at ih
    rw [stdSchedule_succ (k + 1), stdSchedule_succ k, List.map_cons, List.map_cons,
      Desc.alternates, ih, Bool.and_true]
    have : ¬ ((k + 1) % 2 = 0 ↔ k % 2 = 0) := by omega
    by_cases h : k % 2 = 0 <;> simp_all

theorem alternates_of_dirs {k : ℕ} {ms : List Message} (h : ms.map Message.dir = stdSchedule k) :
    Desc.alternates ms = true := by
  rw [alternates_congr ms ((stdSchedule k).map fun dir => (⟨dir, 0⟩ : Message)) (by
    rw [h, List.map_map]; simp [Function.comp_def])]
  exact alternates_canon k

/-- **The padded description is valid.** -/
theorem padDesc_valid (hd : d.Valid) {m : ℕ} (hs : d.HasSchedule m) : (padDesc d s).Valid := by
  unfold Desc.Valid Desc.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hd.out_lt, alternates_of_dirs (dirs_padDesc hs)⟩, ?_⟩, ?_⟩
  · have := hd.blocks_length
    simp [padDesc, length_dummyMsgs, Desc.numMsgs] at this ⊢
    omega
  · refine blocksOkFrom_of _ 0 fun i g hg => ?_
    rw [zero_add]
    by_cases hi : i < s
    · rw [blocks_padDesc_getD_lt hi] at hg; simp at hg
    · obtain ⟨j, rfl⟩ : ∃ j, i = s + j := ⟨i - s, by omega⟩
      rw [blocks_padDesc_getD] at hg
      have := blocksOkFrom_getD d.blocks 0 j hd.blocksOk g hg
      rw [zero_add] at this
      rwa [show (padDesc d s).held (s + j) = d.held j from funext (held_padDesc j)]

/-! ## Wires, registers and blocks -/

variable (d s) in
/-- The wires of `padDesc d s` are those of `d`. -/
def eW : Fin (padDesc d s).totalWires ≃ Fin d.totalWires := finCongr totalWires_padDesc

variable (d s) in
/-- Basis labels of `padDesc d s` are those of `d`. -/
def eQ : Qubits (padDesc d s).totalWires ≃ Qubits d.totalWires :=
  Equiv.arrowCongr (eW d s) (Equiv.refl Bool)

theorem eW_val (w : Fin (padDesc d s).totalWires) : (eW d s w : ℕ) = w := rfl

theorem eQ_apply (y : Qubits (padDesc d s).totalWires) (v : Fin d.totalWires) :
    eQ d s y v = y ((eW d s).symm v) := rfl

theorem inReg_padDesc (j : ℕ) (w : Fin (padDesc d s).totalWires) :
    inReg (padDesc d s) (s + j) w ↔ inReg d j (eW d s w) := by
  unfold inReg
  rw [msgOffset_padDesc, msgWidth_padDesc, eW_val]

theorem not_inReg_padDesc_lt {i : ℕ} (hi : i < s) (w : Fin (padDesc d s).totalWires) :
    ¬ inReg (padDesc d s) i w := by
  unfold inReg
  rw [msgWidth_padDesc_lt hi]
  omega

variable (d s) in
/-- Register `s + j` of `padDesc d s` is register `j` of `d`. -/
def τP (j : ℕ) : Reg (padDesc d s) (s + j) ≃ Reg d j :=
  Equiv.arrowCongr ((eW d s).subtypeEquiv fun w => inReg_padDesc j w) (Equiv.refl Bool)

theorem layerMat_cast {N N' : ℕ} (h : N = N') (l : List Gate) :
    layerMat (l.filterMap (Gate.toInstr? N)) =
      (layerMat (l.filterMap (Gate.toInstr? N'))).submatrix
        (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))
        (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) := by
  subst h
  ext a b
  simp [Equiv.arrowCongr_apply]

theorem blockMat_padDesc (j : ℕ) :
    blockMat (padDesc d s) (s + j) = (blockMat d j).submatrix (eQ d s) (eQ d s) := by
  rw [blockMat, blocks_padDesc_getD, layerMat_cast totalWires_padDesc]
  rfl

theorem blockMat_padDesc_lt {i : ℕ} (hi : i < s) : blockMat (padDesc d s) i = 1 := by
  rw [blockMat, blocks_padDesc_getD_lt hi]
  rfl

/-! ## The dummy turns -/

section Shift

variable (T : IsoStrategy (Reg (padDesc d s)) (Reg (padDesc d s)) (padDesc d s).numMsgs)

/-- The empty register value. -/
def zReg (i : ℕ) : Reg (padDesc d s) i := fun _ => false

theorem reg_eq_zero {i : ℕ} (hi : i < s) (g : Reg (padDesc d s) i) : g = zReg i :=
  funext fun w => absurd w.2 (not_inReg_padDesc_lt hi w.1)

/-- A dummy turn, as a map on memories. -/
noncomputable def dummyW (i : ℕ) : Matrix (T.M (i + 1)) (T.M i) ℂ :=
  Matrix.of fun ν' ν => T.V i (zReg i, ν') (zReg i, ν)

/-- The memory after the first `i` dummy turns. -/
noncomputable def dummyMem : ∀ i, T.M i → ℂ
  | 0 => T.init
  | i + 1 => dummyW T i *ᵥ dummyMem i

theorem dummyW_iso {i : ℕ} (hi : i < s) : (dummyW T i)ᴴ * dummyW T i = 1 := by
  have hV := T.V_iso i (by rw [numMsgs_padDesc]; omega)
  have : Subsingleton (Reg (padDesc d s) i) :=
    ⟨fun a b => (reg_eq_zero hi a).trans (reg_eq_zero hi b).symm⟩
  ext ν ν₂
  have := congrArg (fun M => M (zReg i, ν) (zReg i, ν₂)) hV
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, one_apply, Prod.mk.injEq,
    true_and] at this
  rw [Fintype.sum_subsingleton _ (zReg i)] at this
  simpa [mul_apply, dummyW, one_apply] using this

theorem isDensity_dummyMem : ∀ i ≤ s, IsDensity (pureState (dummyMem T i))
  | 0, _ => T.init_density
  | i + 1, hi => by
    rw [dummyMem, pureState_mulVec]
    exact (isChannel_conjMap (dummyW_iso T (by omega))).map_density
      (isDensity_dummyMem i (by omega))

theorem turnVec_dummy {i : ℕ} (hi : i < s) (u : T.M i → ℂ) (y : Qubits (padDesc d s).totalWires)
    (ν' : T.M (i + 1)) :
    turnVec T i (fun p => zeroVec _ p.1 * u p.2) (y, ν') = zeroVec _ y * (dummyW T i *ᵥ u) ν' := by
  have : Subsingleton (Reg (padDesc d s) i) :=
    ⟨fun a b => (reg_eq_zero hi a).trans (reg_eq_zero hi b).symm⟩
  rw [PrefixData.turnVec_apply, Fintype.sum_subsingleton _ (zReg i),
    reg_eq_zero hi (wireSplitE _ i y).2,
    show PrefixData.regSet (padDesc d s) i y (zReg i) = y from funext fun w => by
      rw [PrefixData.regSet_apply, dif_neg (not_inReg_padDesc_lt hi w)]]
  simp only [mulVec, dotProduct, dummyW, of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem pureRun_dummy : ∀ i < s, ∀ y ν, pureRun T i (y, ν) = zeroVec _ y * dummyMem T i ν
  | 0, hi, y, ν => by
    rw [pureRun, blockMat_padDesc_lt hi, one_kronecker_one, one_mulVec]
    rfl
  | i + 1, hi, y, ν => by
    have ih : pureRun T i = fun p => zeroVec _ p.1 * dummyMem T i p.2 :=
      funext fun p => pureRun_dummy i (by omega) p.1 p.2
    rw [pureRun, blockMat_padDesc_lt hi, one_kronecker_one, one_mulVec, ih, turnVec_dummy T (by omega)]
    rfl

theorem pureRun_padStart :
    pureRun T s = (blockMat (padDesc d s) s ⊗ₖ (1 : Matrix (T.M s) (T.M s) ℂ)) *ᵥ
      fun p => zeroVec _ p.1 * dummyMem T s p.2 := by
  cases s with
  | zero => rfl
  | succ s =>
    have ih : pureRun T s = fun p => zeroVec _ p.1 * dummyMem T s p.2 :=
      funext fun p => pureRun_dummy T s (by omega) p.1 p.2
    rw [pureRun, ih]
    congr 1
    funext p
    rw [turnVec_dummy T (by omega)]
    rfl

/-- **The shifted prover**: the first `s` turns become the initial memory. -/
@[reducible] noncomputable def shiftT : IsoStrategy (Reg d) (Reg d) d.numMsgs where
  M j := T.M (s + j)
  init := dummyMem T s
  init_density := isDensity_dummyMem T s le_rfl
  V j := (T.V (s + j)).submatrix (Prod.map (τP d s j).symm id) (Prod.map (τP d s j).symm id)
  V_iso j hj := iso_submatrix_equiv (T.V (s + j))
    (T.V_iso (s + j) (by rw [numMsgs_padDesc]; omega))
    ((τP d s j).symm.prodCongr (Equiv.refl _)) ((τP d s j).symm.prodCongr (Equiv.refl _))

theorem split_τP (j : ℕ) (y : Qubits (padDesc d s).totalWires) :
    (τP d s j).symm (wireSplitE d j (eQ d s y)).2 = (wireSplitE (padDesc d s) (s + j) y).2 := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem regSet_τP (j : ℕ) (y : Qubits (padDesc d s).totalWires) (x : Reg (padDesc d s) (s + j)) :
    eQ d s (PrefixData.regSet (padDesc d s) (s + j) y x) =
      PrefixData.regSet d j (eQ d s y) (τP d s j x) := by
  funext v
  rw [eQ_apply, PrefixData.regSet_apply, PrefixData.regSet_apply]
  have hv : inReg (padDesc d s) (s + j) ((eW d s).symm v) ↔ inReg d j v := by
    rw [inReg_padDesc, Equiv.apply_symm_apply]
  by_cases h : inReg d j v
  · rw [dif_pos (hv.mpr h), dif_pos h]
    rfl
  · rw [dif_neg (fun h' => h (hv.mp h')), dif_neg h, eQ_apply]

theorem turnVec_shift (j : ℕ) (v : Qubits (padDesc d s).totalWires × T.M (s + j) → ℂ)
    (v' : Qubits d.totalWires × (shiftT T).M j → ℂ) (hv : ∀ y ν, v (y, ν) = v' (eQ d s y, ν))
    (y : Qubits (padDesc d s).totalWires) (ν' : T.M (s + j + 1)) :
    turnVec T (s + j) v (y, ν') = turnVec (shiftT T) j v' (eQ d s y, ν') := by
  rw [PrefixData.turnVec_apply, PrefixData.turnVec_apply]
  refine Fintype.sum_equiv (τP d s j) _ _ fun x => Finset.sum_congr rfl fun ν _ => ?_
  change _ = T.V (s + j) ((τP d s j).symm (wireSplitE d j (eQ d s y)).2, ν')
    ((τP d s j).symm (τP d s j x), ν) * _
  rw [split_τP, Equiv.symm_apply_apply, hv, regSet_τP]

theorem zeroVec_eQ (z : Qubits d.totalWires) :
    zeroVec (padDesc d s).totalWires ((eQ d s).symm z) = zeroVec d.totalWires z := by
  simp only [zeroVec]
  congr 1
  apply propext
  constructor
  · intro h; funext v
    have := congrFun h ((eW d s).symm v)
    change z (eW d s ((eW d s).symm v)) = _ at this
    rw [Equiv.apply_symm_apply] at this
    exact this
  · intro h; funext w
    rw [h]; rfl

theorem kron_submatrix_mulVec {M : Type} [Fintype M] [DecidableEq M]
    (B : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ)
    (f : Qubits (padDesc d s).totalWires × M → ℂ) (g : Qubits d.totalWires × M → ℂ)
    (hfg : ∀ y μ, f (y, μ) = g (eQ d s y, μ)) (y : Qubits (padDesc d s).totalWires) (μ : M) :
    ((B.submatrix (eQ d s) (eQ d s) ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ f) (y, μ) =
      ((B ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ g) (eQ d s y, μ) := by
  rw [kronOne_mulVec_apply, kronOne_mulVec_apply, submatrix_mulVec_equiv]
  have : (fun y' => f (y', μ)) ∘ (eQ d s).symm = fun y' => g (y', μ) :=
    funext fun z => by simp only [Function.comp_apply, hfg, Equiv.apply_symm_apply]
  rw [Function.comp_apply, this]

/-- **The padded run is the shifted run.** -/
theorem pureRun_shift : ∀ j ≤ d.numMsgs, ∀ y ν,
    pureRun T (s + j) (y, ν) = pureRun (shiftT T) j (eQ d s y, ν)
  | 0, _, y, ν => by
    change pureRun T s (y, ν) = _
    rw [pureRun_padStart, show blockMat (padDesc d s) s = (blockMat d 0).submatrix (eQ d s) (eQ d s)
      from blockMat_padDesc 0]
    refine kron_submatrix_mulVec _ _ _ (fun y μ => ?_) y ν
    change zeroVec _ y * _ = zeroVec _ (eQ d s y) * _
    rw [← zeroVec_eQ (eQ d s y), Equiv.symm_apply_apply]
  | j + 1, hj, y, ν => by
    change pureRun T (s + j + 1) (y, ν) = _
    rw [pureRun, pureRun, show blockMat (padDesc d s) (s + j + 1) =
      (blockMat d (j + 1)).submatrix (eQ d s) (eQ d s) from blockMat_padDesc (j + 1)]
    exact kron_submatrix_mulVec _ _ _ (fun y μ => turnVec_shift T j _ _
      (fun y ν => pureRun_shift j (by omega) y ν) y μ) y ν

theorem outBit_eQ (y : Qubits (padDesc d s).totalWires) :
    outBit (padDesc d s) y ↔ outBit d (eQ d s y) := by
  constructor
  · rintro ⟨h, e⟩
    exact ⟨by rw [← totalWires_padDesc (d := d) (s := s)]; exact h, e⟩
  · rintro ⟨h, e⟩
    exact ⟨by rw [totalWires_padDesc]; exact h, e⟩

/-- **Shifting keeps the acceptance probability.** -/
theorem accept_shiftT : accept T.toOp = accept (shiftT T).toOp := by
  have hacc : ∀ k, k = (padDesc d s).numMsgs → accept T.toOp = (star (pureRun T k) ⬝ᵥ
      (acceptEffect (padDesc d s) (T.M k) *ᵥ pureRun T k)).re := by
    intro k hk; subst hk; exact accept_pureRun T
  rw [hacc _ numMsgs_padDesc.symm, accept_pureRun, accept_expect, accept_expect]
  refine Fintype.sum_equiv (eQ d s) _ _ fun y => Finset.sum_congr rfl fun ν _ => ?_
  rw [pureRun_shift T _ le_rfl]
  by_cases h : outBit (padDesc d s) y
  · rw [if_pos h, if_pos ((outBit_eQ y).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((outBit_eQ y).mpr h'))]

end Shift

/-! ## Waiting provers -/

section Wait

variable (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs)

theorem inReg_padDesc_ge {i : ℕ} (h : s ≤ i) (w : Fin (padDesc d s).totalWires) :
    inReg (padDesc d s) i w ↔ inReg d (i - s) (eW d s w) := by
  have := inReg_padDesc (d := d) (s := s) (i - s) w
  rwa [Nat.add_sub_cancel' h] at this

variable (d s) in
/-- Register `i ≥ s` of `padDesc d s` is register `i - s` of `d`. -/
def ρP {i : ℕ} (h : s ≤ i) : Reg (padDesc d s) i ≃ Reg d (i - s) :=
  Equiv.arrowCongr ((eW d s).subtypeEquiv fun w => inReg_padDesc_ge h w) (Equiv.refl Bool)

/-- Memories, by index equality. -/
def mCast {i i' : ℕ} (h : i = i') : T₀.M i ≃ T₀.M i' := Equiv.cast (congrArg T₀.M h)

/-- The turns of the waiting prover. -/
noncomputable def waitV (i : ℕ) :
    Matrix (Reg (padDesc d s) i × T₀.M (i + 1 - s)) (Reg (padDesc d s) i × T₀.M (i - s)) ℂ :=
  if h : s ≤ i then
    (T₀.V (i - s)).submatrix (Prod.map (ρP d s h) (mCast T₀ (by omega)))
      (Prod.map (ρP d s h) (Equiv.refl _))
  else
    (1 : Matrix (Reg (padDesc d s) i × T₀.M (i - s)) (Reg (padDesc d s) i × T₀.M (i - s)) ℂ).submatrix
      (Prod.map id (mCast T₀ (by omega))) id

theorem waitV_iso {i : ℕ} (hi : i < (padDesc d s).numMsgs) :
    (waitV T₀ (s := s) i)ᴴ * waitV T₀ (s := s) i = 1 := by
  unfold waitV
  split_ifs with h
  · exact iso_submatrix_equiv _ (T₀.V_iso (i - s) (by rw [numMsgs_padDesc] at hi; omega))
      ((ρP d s h).prodCongr (mCast T₀ (by omega))) ((ρP d s h).prodCongr (Equiv.refl _))
  · exact iso_submatrix_equiv _ (by rw [conjTranspose_one, Matrix.one_mul])
      ((Equiv.refl _).prodCongr (mCast T₀ (by omega))) (Equiv.refl _)

/-- **The waiting prover**: idle for `s` turns, then `T₀`. -/
@[reducible] noncomputable def waitT : IsoStrategy (Reg (padDesc d s)) (Reg (padDesc d s)) (padDesc d s).numMsgs where
  M i := T₀.M (i - s)
  init := T₀.init ∘ mCast T₀ (Nat.zero_sub s)
  init_density := isDensity_pureState_comp _ T₀.init_density _
  V i := waitV T₀ i
  V_iso _ hi := waitV_iso T₀ hi

theorem cast_mCast {i i' i'' : ℕ} (h : i = i') (h' : i' = i'') (a : T₀.M i) :
    mCast T₀ h' (mCast T₀ h a) = mCast T₀ (h.trans h') a := by
  subst h; subst h'; rfl

theorem dummyMem_waitT : ∀ (i : ℕ) (hi : i ≤ s) (a : T₀.M (i - s)),
    dummyMem (waitT T₀ (s := s)) i a = T₀.init (mCast T₀ (Nat.sub_eq_zero_of_le hi) a)
  | 0, _, a => rfl
  | i + 1, hi, a => by
    have hlt : ¬ s ≤ i := by omega
    rw [dummyMem]
    simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single (mCast T₀ (by omega : i + 1 - s = i - s) a)]
    · rw [dummyMem_waitT i (by omega), cast_mCast]
      change waitV T₀ i (zReg i, a) (zReg i, _) * _ = _
      rw [waitV, dif_neg hlt]
      simp [Prod.map_apply, Matrix.one_apply]
    · intro ν _ hν
      change waitV T₀ i (zReg i, a) (zReg i, ν) * _ = 0
      rw [waitV, dif_neg hlt]
      simp [Ne.symm hν]
    · simp

theorem V_transport {k k' : ℕ} (e : k = k') (x x' : Reg d k) (a : T₀.M (k + 1)) (b : T₀.M k) :
    T₀.V k (x, a) (x', b) = T₀.V k' (Equiv.cast (congrArg (Reg d) e) x, mCast T₀ (by omega) a)
      (Equiv.cast (congrArg (Reg d) e) x', mCast T₀ e b) := by
  subst e; rfl

theorem regCast_apply {k k' : ℕ} (e : k = k') (f : Reg d k) (w : Fin d.totalWires)
    (hw : inReg d k' w) : Equiv.cast (congrArg (Reg d) e) f ⟨w, hw⟩ = f ⟨w, e ▸ hw⟩ := by
  subst e; rfl

theorem shift_waitT_V (j : ℕ) (_hj : j < d.numMsgs) (g : Reg d j) (a : T₀.M (s + (j + 1) - s))
    (g' : Reg d j) (b : T₀.M (s + j - s)) :
    (shiftT (waitT T₀ (s := s))).V j (g, a) (g', b) =
      T₀.V j (g, mCast T₀ (by omega) a) (g', mCast T₀ (by omega) b) := by
  change waitV T₀ (s + j) ((τP d s j).symm g, a) ((τP d s j).symm g', b) = _
  rw [waitV, dif_pos (by omega)]
  simp only [submatrix_apply, Prod.map_apply, Equiv.refl_apply]
  rw [V_transport T₀ (Nat.add_sub_cancel_left s j)]
  simp only [cast_mCast]
  congr 2
  · funext ⟨w, hw⟩
    rw [regCast_apply (Nat.add_sub_cancel_left s j)]
    rfl
  · funext ⟨w, hw⟩
    rw [regCast_apply (Nat.add_sub_cancel_left s j)]
    rfl

/-- **Waiting keeps the acceptance probability.** -/
theorem accept_waitT : accept (waitT T₀ (s := s)).toOp = accept T₀.toOp := by
  rw [accept_shiftT]
  refine accept_relabel T₀ (shiftT (waitT T₀ (s := s))) (fun _ _ => mCast T₀ (by omega))
    (fun a => ?_) (fun j hj g a g' b => shift_waitT_V T₀ j hj g a g' b)
  exact dummyMem_waitT T₀ s le_rfl a

end Wait

/-! ## The value -/

/-- **Padding does not change the value.** -/
theorem value_padDesc : value (padDesc d s) = value d := by
  apply le_antisymm
  · obtain ⟨P, hP⟩ := value_attained (padDesc d s)
    obtain ⟨T, hT⟩ := exists_isoProver P
    rw [← hP, ← hT, accept_shiftT]
    exact accept_le_value d _
  · obtain ⟨P, hP⟩ := value_attained d
    obtain ⟨T₀, hT₀⟩ := exists_isoProver P
    rw [← hP, ← hT₀, ← accept_waitT T₀ (s := s)]
    exact accept_le_value _ _

/-- **Every acceptance probability of `d` is one of the padded description.** -/
theorem exists_accept_padDesc (P : Prover d) : ∃ P' : Prover (padDesc d s), accept P' = accept P := by
  obtain ⟨T₀, hT₀⟩ := exists_isoProver P
  exact ⟨(waitT T₀ (s := s)).toOp, by rw [accept_waitT, hT₀]⟩

/-! ## Padding to `2^(r+1) + 1` messages -/

section PadTo

open Arith

/-- **Pad to `padCount m` messages**, the first count of the form `2^(r+1) + 1` that is `≥ m`. -/
def padTo (d : Desc) : Desc := padDesc d (padCount d.numMsgs - d.numMsgs)

theorem numMsgs_padTo : (padTo d).numMsgs = padCount d.numMsgs := by
  rw [padTo, numMsgs_padDesc]
  have := le_padCount d.numMsgs
  omega

theorem hasSchedule_padTo {m : ℕ} (hs : d.HasSchedule m) : (padTo d).HasSchedule (padCount m) := by
  have hm := Desc.numMsgs_of_hasSchedule hs
  have h := hasSchedule_padDesc (s := padCount d.numMsgs - d.numMsgs) hs
  rw [hm, Nat.add_sub_cancel' (le_padCount m)] at h
  unfold padTo; rw [hm]; exact h

theorem padTo_valid (hd : d.Valid) {m : ℕ} (hs : d.HasSchedule m) : (padTo d).Valid :=
  padDesc_valid hd hs

theorem value_padTo : value (padTo d) = value d := value_padDesc

theorem totalWires_padTo : (padTo d).totalWires = d.totalWires := totalWires_padDesc

theorem exists_accept_padTo (P : Prover d) : ∃ P' : Prover (padTo d), accept P' = accept P :=
  exists_accept_padDesc P

end PadTo

end ShiQIP
