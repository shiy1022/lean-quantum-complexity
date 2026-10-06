/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Circuit.Controlled

/-!
# Relabelling the wires of a circuit

An injective wire map `f : Fin N ↪ Fin M` places an `N`-wire circuit on `M` wires.

* `embSplit f : Qubits M ≃ Qubits N × (Outside f → Bool)` splits a basis label into the wires in
  the image of `f` and the rest.
* `instrMap f` relabels one instruction; **`runLayer_map`** says the relabelled circuit acts as
  the original on the image wires, separately for each value of the remaining wires.
* **`layerMat_map`**: `layerMat (l.map (instrMap f)) = (layerMat l ⊗ 1).submatrix s s`, with
  `s = embSplit f`.
* On description syntax, `Gate.relabel` relabels a gate by a map `ℕ → ℕ`;
  `filterMap_relabel` shows that translating then relabelling equals relabelling then
  translating, for gates in range.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

variable {N M : ℕ}

/-- The wires outside the image of `f`. -/
abbrev Outside (f : Fin N ↪ Fin M) : Type := {w : Fin M // w ∉ Set.range f}

/-- Split a basis label into its image wires and the rest. -/
noncomputable def embSplit (f : Fin N ↪ Fin M) : Qubits M ≃ Qubits N × (Outside f → Bool) where
  toFun y := (fun i => y (f i), fun r => y r.1)
  invFun p w := if h : ∃ i, f i = w then p.1 (Classical.choose h) else p.2 ⟨w, by simpa using h⟩
  left_inv y := by
    funext w
    by_cases h : ∃ i, f i = w
    · simp only [dif_pos h]; rw [Classical.choose_spec h]
    · simp only [dif_neg h]
  right_inv p := by
    refine Prod.ext (funext fun i => ?_) (funext fun r => ?_)
    · have h : ∃ i', f i' = f i := ⟨i, rfl⟩
      simp only [dif_pos h]
      rw [f.injective (Classical.choose_spec h)]
    · have h : ¬ ∃ i, f i = r.1 := fun ⟨i, hi⟩ => r.2 ⟨i, hi⟩
      simp only [dif_neg h]

theorem embSplit_fst (f : Fin N ↪ Fin M) (y : Qubits M) (i : Fin N) :
    (embSplit f y).1 i = y (f i) := rfl

theorem embSplit_snd (f : Fin N ↪ Fin M) (y : Qubits M) (r : Outside f) :
    (embSplit f y).2 r = y r.1 := rfl

theorem embSplit_update (f : Fin N ↪ Fin M) (y : Qubits M) (i : Fin N) (b : Bool) :
    embSplit f (Function.update y (f i) b) =
      (Function.update (embSplit f y).1 i b, (embSplit f y).2) := by
  refine Prod.ext ?_ (funext fun r => ?_)
  · exact Function.update_comp_eq_of_injective y f.injective i b
  · have : r.1 ≠ f i := fun e => r.2 ⟨i, e.symm⟩
    exact Function.update_of_ne this _ _

theorem embSplit_symm_update (f : Fin N ↪ Fin M) (y : Qubits M) (i : Fin N) (b : Bool) :
    (embSplit f).symm (Function.update (embSplit f y).1 i b, (embSplit f y).2) =
      Function.update y (f i) b := by
  rw [Equiv.symm_apply_eq, embSplit_update]

/-! ## Relabelled instructions -/

/-- Relabel one instruction. -/
def instrMap (f : Fin N ↪ Fin M) : Instr N → Instr M
  | .h i => .h (f i)
  | .s i => .s (f i)
  | .t i => .t (f i)
  | .x i => .x (f i)
  | .cnot i j h => .cnot (f i) (f j) (fun e => h (f.injective e))

/-- The slice of `ψ` at a fixed value `z` of the outside wires. -/
noncomputable def sliceAt (f : Fin N ↪ Fin M) (ψ : QState M) (z : Outside f → Bool) : QState N :=
  fun x => ψ ((embSplit f).symm (x, z))

theorem apply1_map (f : Fin N ↪ Fin M) (U : Matrix Bool Bool ℂ) (i : Fin N) (ψ : QState M)
    (y : Qubits M) :
    apply1 U (f i) ψ y = apply1 U i (sliceAt f ψ (embSplit f y).2) (embSplit f y).1 := by
  simp only [apply1, sliceAt, embSplit_symm_update, embSplit_fst]

/-- **One relabelled instruction** acts as the original one on each slice. -/
theorem instrMap_apply (f : Fin N ↪ Fin M) (g : Instr N) (ψ : QState M) (y : Qubits M) :
    (instrMap f g).apply ψ y = g.apply (sliceAt f ψ (embSplit f y).2) (embSplit f y).1 := by
  cases g with
  | h i => exact apply1_map f _ i ψ y
  | s i => exact apply1_map f _ i ψ y
  | t i => exact apply1_map f _ i ψ y
  | x i => exact apply1_map f _ i ψ y
  | cnot i j hij =>
    change ψ (Function.update y (f j) (xor (y (f j)) (y (f i)))) =
      ψ ((embSplit f).symm (Function.update (embSplit f y).1 j
        (xor ((embSplit f y).1 j) ((embSplit f y).1 i)), (embSplit f y).2))
    rw [embSplit_symm_update]
    rfl

theorem sliceAt_apply (f : Fin N ↪ Fin M) (g : Instr N) (ψ : QState M) (z : Outside f → Bool) :
    sliceAt f ((instrMap f g).apply ψ) z = g.apply (sliceAt f ψ z) := by
  funext x
  simp only [sliceAt, instrMap_apply, Equiv.apply_symm_apply]

/-- **A relabelled circuit** acts as the original circuit on each slice. -/
theorem runLayer_map (f : Fin N ↪ Fin M) :
    ∀ (l : List (Instr N)) (ψ : QState M) (z : Outside f → Bool),
      sliceAt f (runLayer (l.map (instrMap f)) ψ) z = runLayer l (sliceAt f ψ z)
  | [], _, _ => rfl
  | g :: l, ψ, z => by
    rw [List.map_cons, runLayer_cons, runLayer_cons, runLayer_map f l, sliceAt_apply]

theorem runLayer_map_apply (f : Fin N ↪ Fin M) (l : List (Instr N)) (ψ : QState M)
    (y : Qubits M) :
    runLayer (l.map (instrMap f)) ψ y =
      runLayer l (sliceAt f ψ (embSplit f y).2) (embSplit f y).1 := by
  rw [← runLayer_map f l ψ (embSplit f y).2]
  simp only [sliceAt, Prod.mk.eta, Equiv.symm_apply_apply]

/-- **The matrix of a relabelled circuit.** -/
theorem layerMat_map (f : Fin N ↪ Fin M) (l : List (Instr N)) :
    layerMat (l.map (instrMap f)) =
      (layerMat l ⊗ₖ (1 : Matrix (Outside f → Bool) (Outside f → Bool) ℂ)).submatrix
        (embSplit f) (embSplit f) := by
  ext y y'
  have h := congrFun (layerMat_mulVec (l.map (instrMap f)) (Pi.single y' 1)) y
  rw [mulVec_single_one] at h
  change (layerMat (l.map (instrMap f))) y y' = _
  rw [show layerMat (l.map (instrMap f)) y y' = (layerMat (l.map (instrMap f))).col y' y from rfl,
    h, runLayer_map_apply, ← layerMat_mulVec]
  simp only [mulVec, dotProduct, sliceAt, submatrix_apply, kroneckerMap_apply, one_apply]
  have hs : ∀ x, (Pi.single y' (1 : ℂ) : QState M) ((embSplit f).symm (x, (embSplit f y).2)) =
      if x = (embSplit f y').1 ∧ (embSplit f y).2 = (embSplit f y').2 then 1 else 0 := by
    intro x
    rw [Pi.single_apply]
    have : ((embSplit f).symm (x, (embSplit f y).2) = y') ↔
        (x = (embSplit f y').1 ∧ (embSplit f y).2 = (embSplit f y').2) := by
      rw [Equiv.symm_apply_eq, Prod.mk.injEq]
    by_cases hc : x = (embSplit f y').1 ∧ (embSplit f y).2 = (embSplit f y').2
    · rw [if_pos (this.mpr hc), if_pos hc]
    · rw [if_neg (fun e => hc (this.mp e)), if_neg hc]
  simp only [hs, mul_ite, mul_one, mul_zero]
  by_cases hz : (embSplit f y).2 = (embSplit f y').2
  · simp [hz]
  · simp [hz]

/-! ## Description syntax -/

/-- Relabel a gate by a wire map. -/
def Gate.relabel (τ : ℕ → ℕ) : Gate → Gate
  | .h i => .h (τ i)
  | .s i => .s (τ i)
  | .t i => .t (τ i)
  | .x i => .x (τ i)
  | .cnot i j => .cnot (τ i) (τ j)

theorem Gate.wires_relabel (τ : ℕ → ℕ) (g : Gate) : (g.relabel τ).wires = g.wires.map τ := by
  cases g <;> rfl

/-- **Translation commutes with relabelling** for an in-range gate. -/
theorem toInstr?_relabel (f : Fin N ↪ Fin M) (τ : ℕ → ℕ) (hτ : ∀ i : Fin N, τ i = f i)
    {g : Gate} {ι : Instr N} (hg : g.toInstr? N = some ι) :
    (g.relabel τ).toInstr? M = some (instrMap f ι) := by
  cases g with
  | h i => simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
           simp [Gate.relabel, Gate.toInstr?, hτ ⟨i, hi⟩, instrMap]
  | s i => simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
           simp [Gate.relabel, Gate.toInstr?, hτ ⟨i, hi⟩, instrMap]
  | t i => simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
           simp [Gate.relabel, Gate.toInstr?, hτ ⟨i, hi⟩, instrMap]
  | x i => simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
           simp [Gate.relabel, Gate.toInstr?, hτ ⟨i, hi⟩, instrMap]
  | cnot i j =>
    simp only [Gate.toInstr?] at hg; split_ifs at hg with hij; cases hg
    have hne : (f ⟨i, hij.1⟩ : ℕ) ≠ f ⟨j, hij.2.1⟩ := fun e =>
      hij.2.2 (congrArg Fin.val (f.injective (Fin.ext e)))
    simp [Gate.relabel, Gate.toInstr?, hτ ⟨i, hij.1⟩, hτ ⟨j, hij.2.1⟩, instrMap, hne]

theorem filterMap_relabel (f : Fin N ↪ Fin M) (τ : ℕ → ℕ) (hτ : ∀ i : Fin N, τ i = f i) :
    ∀ (gs : List Gate), (∀ g ∈ gs, (g.toInstr? N).isSome) →
      (gs.map (Gate.relabel τ)).filterMap (Gate.toInstr? M) =
        (gs.filterMap (Gate.toInstr? N)).map (instrMap f)
  | [], _ => rfl
  | g :: gs, h => by
    obtain ⟨ι, hι⟩ := Option.isSome_iff_exists.mp (h g List.mem_cons_self)
    rw [List.map_cons, List.filterMap_cons, toInstr?_relabel f τ hτ hι, List.filterMap_cons, hι,
      filterMap_relabel f τ hτ gs fun g' hg' => h g' (List.mem_cons_of_mem _ hg')]
    rfl

end ShiQIP
