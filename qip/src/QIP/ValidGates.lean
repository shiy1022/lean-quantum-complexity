/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.ShiShallowBridge

/-!
# Valid descriptions drop no gates

`blockMat d j` translates the gates of block `j` with `Gate.toInstr?` and drops any gate whose
wires are out of range (or a CNOT with equal wires). For a **valid** description no gate is
dropped:

* `Valid.toInstr?_isSome`: every gate of every block translates;
* `Valid.map_toGate_filterMap`: translating block `j` and mapping back with `Instr.toGate` gives
  exactly the original gate list, so `blockMat d j` is the circuit of the written gates.
-/

namespace ShiQIP

open ShiShallow

theorem toGate_of_toInstr? {N : ℕ} {g : Gate} {i : Instr N} (h : g.toInstr? N = some i) :
    i.toGate = g := by
  cases g with
  | h w => simp only [Gate.toInstr?] at h; split_ifs at h; cases h; rfl
  | s w => simp only [Gate.toInstr?] at h; split_ifs at h; cases h; rfl
  | t w => simp only [Gate.toInstr?] at h; split_ifs at h; cases h; rfl
  | x w => simp only [Gate.toInstr?] at h; split_ifs at h; cases h; rfl
  | cnot a b => simp only [Gate.toInstr?] at h; split_ifs at h; cases h; rfl

theorem okBool_range {ok : ℕ → Bool} {W : ℕ} (hok : ∀ w, ok w = true → w < W) {g : Gate}
    (hg : g.okBool ok = true) : g.okBool (fun w => decide (w < W)) = true := by
  cases g <;> simp only [Gate.okBool, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hg ⊢
  · exact hok _ hg
  · exact hok _ hg
  · exact hok _ hg
  · exact hok _ hg
  · exact ⟨⟨hok _ hg.1.1, hok _ hg.1.2⟩, hg.2⟩

theorem blocksOkFrom_getD {d : Desc} :
    ∀ (bs : List (List Gate)) (j₀ i : ℕ), d.blocksOkFrom bs j₀ = true →
      ∀ g ∈ bs.getD i [], g.okBool (d.held (j₀ + i)) = true
  | [], _, i, _, g, hg => by simp at hg
  | b :: bs, j₀, i, h, g, hg => by
    simp only [Desc.blocksOkFrom, Bool.and_eq_true, List.all_eq_true] at h
    cases i with
    | zero => simpa using h.1 g (by simpa using hg)
    | succ i =>
      have := blocksOkFrom_getD bs (j₀ + 1) i h.2 g (by simpa using hg)
      rwa [show j₀ + 1 + i = j₀ + (i + 1) by omega] at this

/-- **Every gate of a valid description translates.** -/
theorem Desc.Valid.toInstr?_isSome {d : Desc} (hd : d.Valid) (j : ℕ) :
    ∀ g ∈ d.blocks.getD j [], (g.toInstr? d.totalWires).isSome := by
  intro g hg
  have := blocksOkFrom_getD d.blocks 0 j hd.blocksOk g hg
  rw [Gate.toInstr?_isSome_iff]
  exact okBool_range (fun w hw => Desc.held_lt hw) this

theorem map_toGate_filterMap {N : ℕ} :
    ∀ (l : List Gate), (∀ g ∈ l, (g.toInstr? N).isSome) →
      (l.filterMap (Gate.toInstr? N)).map Instr.toGate = l
  | [], _ => rfl
  | g :: l, h => by
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (h g List.mem_cons_self)
    rw [List.filterMap_cons, hi, List.map_cons, toGate_of_toInstr? hi,
      map_toGate_filterMap l fun g' hg' => h g' (List.mem_cons_of_mem _ hg')]

/-- **No gate of a valid description is dropped**: block `j`'s translated instructions are
exactly its written gates. -/
theorem Desc.Valid.map_toGate_filterMap {d : Desc} (hd : d.Valid) (j : ℕ) :
    ((d.blocks.getD j []).filterMap (Gate.toInstr? d.totalWires)).map Instr.toGate =
      d.blocks.getD j [] :=
  ShiQIP.map_toGate_filterMap _ (hd.toInstr?_isSome j)

theorem Desc.Valid.length_filterMap {d : Desc} (hd : d.Valid) (j : ℕ) :
    ((d.blocks.getD j []).filterMap (Gate.toInstr? d.totalWires)).length =
      (d.blocks.getD j []).length := by
  conv_rhs => rw [← hd.map_toGate_filterMap j]
  rw [List.length_map]

end ShiQIP
