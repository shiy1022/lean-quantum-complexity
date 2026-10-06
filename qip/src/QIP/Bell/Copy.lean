/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Final

/-!
# Q27 — the copy-and-ship layer

`bellG d` is `CNOT(out → B)` followed by the swap of every wire `x` of `d` (at `bellShift x`)
with wire `x` of message `m` (at `W + 2 + x`). On basis labels (**`bellG_mulVec`**):
`(G v) y = v (cnot (y ∘ σ))` where `σ` exchanges the two copies (`σ_sw`, `σ_mw`) and fixes
every other wire (`σ_fix`).
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

variable {d : Desc}

theorem bellShift_lt_msgOff {x : ℕ} (hx : x < d.totalWires) : bellShift d x < bellMsgOff d := by
  unfold bellShift bellMsgOff; split_ifs <;> omega

variable (d) in
/-- Wire `x` of `d` inside `bellDesc d`. -/
def sw (x : Fin d.totalWires) : Fin (bellDesc d).totalWires := bellEmb d x

variable (d) in
/-- Wire `x` of message `m`. -/
def mw (x : Fin d.totalWires) : Fin (bellDesc d).totalWires :=
  ⟨bellMsgOff d + x, by rw [totalWires_bellDesc]; unfold bellMsgOff; omega⟩

theorem sw_val (x : Fin d.totalWires) : (sw d x : ℕ) = bellShift d x := rfl
theorem mw_val (x : Fin d.totalWires) : (mw d x : ℕ) = bellMsgOff d + x := rfl

theorem sw_ne_mw (x x' : Fin d.totalWires) : sw d x ≠ mw d x' := fun h => by
  have := congrArg Fin.val h; rw [sw_val, mw_val] at this
  have := bellShift_lt_msgOff (d := d) x.2; omega

theorem sw_inj {x x' : Fin d.totalWires} (h : sw d x = sw d x') : x = x' :=
  (bellEmb d).injective h

theorem mw_inj {x x' : Fin d.totalWires} (h : mw d x = mw d x') : x = x' :=
  Fin.ext (by have := congrArg Fin.val h; rw [mw_val, mw_val] at this; omega)

variable (d) in
/-- The first `k` swaps, composed. -/
def σ : ℕ → Equiv.Perm (Fin (bellDesc d).totalWires)
  | 0 => 1
  | k + 1 => (if h : k < d.totalWires then Equiv.swap (sw d ⟨k, h⟩) (mw d ⟨k, h⟩) else 1) * σ k

theorem σ_sw : ∀ (k : ℕ) (x : Fin d.totalWires), σ d k (sw d x) = if (x : ℕ) < k then mw d x else sw d x
  | 0, x => by simp [σ]
  | k + 1, x => by
    rw [σ, Equiv.Perm.mul_apply, σ_sw k x]
    by_cases hk : k < d.totalWires
    · rw [dif_pos hk]
      by_cases hxk : (x : ℕ) < k
      · rw [if_pos hxk, if_pos (by omega)]
        refine Equiv.swap_apply_of_ne_of_ne (Ne.symm (sw_ne_mw _ _)) (fun h => ?_)
        have := congrArg Fin.val (mw_inj h); simp at this; omega
      · by_cases hxe : (x : ℕ) = k
        · rw [if_neg hxk, if_pos (by omega)]
          have : x = ⟨k, hk⟩ := Fin.ext hxe
          subst this
          exact Equiv.swap_apply_left _ _
        · rw [if_neg hxk, if_neg (by omega)]
          refine Equiv.swap_apply_of_ne_of_ne (fun h => hxe ?_) (sw_ne_mw _ _)
          exact congrArg Fin.val (sw_inj h)
    · rw [dif_neg hk, Equiv.Perm.one_apply]
      have : ¬ (x : ℕ) = k := by have := x.2; omega
      split_ifs <;> first | rfl | omega

theorem σ_mw : ∀ (k : ℕ) (x : Fin d.totalWires), σ d k (mw d x) = if (x : ℕ) < k then sw d x else mw d x
  | 0, x => by simp [σ]
  | k + 1, x => by
    rw [σ, Equiv.Perm.mul_apply, σ_mw k x]
    by_cases hk : k < d.totalWires
    · rw [dif_pos hk]
      by_cases hxk : (x : ℕ) < k
      · rw [if_pos hxk, if_pos (by omega)]
        refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) (sw_ne_mw _ _)
        have := congrArg Fin.val (sw_inj h); simp at this; omega
      · by_cases hxe : (x : ℕ) = k
        · rw [if_neg hxk, if_pos (by omega)]
          have : x = ⟨k, hk⟩ := Fin.ext hxe
          subst this
          exact Equiv.swap_apply_right _ _
        · rw [if_neg hxk, if_neg (by omega)]
          refine Equiv.swap_apply_of_ne_of_ne (Ne.symm (sw_ne_mw _ _)) (fun h => hxe ?_)
          exact congrArg Fin.val (mw_inj h)
    · rw [dif_neg hk, Equiv.Perm.one_apply]
      have : ¬ (x : ℕ) = k := by have := x.2; omega
      split_ifs <;> first | rfl | omega

theorem σ_fix (k : ℕ) (w : Fin (bellDesc d).totalWires) (h1 : ∀ x, w ≠ sw d x)
    (h2 : ∀ x, w ≠ mw d x) : σ d k w = w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [σ, Equiv.Perm.mul_apply, ih]
    split_ifs with hk
    · exact Equiv.swap_apply_of_ne_of_ne (h1 _) (h2 _)
    · rfl

/-- The instructions of the first `k` swaps. -/
noncomputable def swapsUpTo (k : ℕ) : List (Instr (bellDesc d).totalWires) :=
  ((List.range k).flatMap fun x => swapGates (bellShift d x) (bellMsgOff d + x)).filterMap
    (Gate.toInstr? (bellDesc d).totalWires)

theorem runLayer_swapsUpTo : ∀ k ≤ d.totalWires, ∀ ψ : QState (bellDesc d).totalWires,
    runLayer (swapsUpTo (d := d) k) ψ = fun y => ψ (y ∘ σ d k)
  | 0, _, ψ => by funext y; simp [swapsUpTo, σ, runLayer_nil]
  | k + 1, hk, ψ => by
    have hk' : k < d.totalWires := by omega
    have hs : (swapGates (bellShift d k) (bellMsgOff d + k)).filterMap
        (Gate.toInstr? (bellDesc d).totalWires) =
          swapInstrs (sw d ⟨k, hk'⟩) (mw d ⟨k, hk'⟩) (sw_ne_mw _ _) :=
      filterMap_swapGates (sw d ⟨k, hk'⟩) (mw d ⟨k, hk'⟩) (sw_ne_mw _ _)
    rw [swapsUpTo, List.range_succ, List.flatMap_append, List.filterMap_append,
      List.flatMap_singleton, hs, runLayer_append, ← swapsUpTo, runLayer_swapsUpTo k (by omega),
      runLayer_swapInstrs]
    funext y
    rw [show σ d (k + 1) = _ * σ d k from rfl, dif_pos hk']
    rfl

theorem out_lt_W (hd : d.Valid) : d.out < d.totalWires := by
  have := hd.out_lt; have := priv_le_totalWires d; omega

theorem sw_out_ne_wB (hd : d.Valid) : sw d ⟨d.out, out_lt_W hd⟩ ≠ wB d := fun h => by
  have h1 := congrArg Fin.val h; have h2 := hd.out_lt
  change bellShift d d.out = bellB d at h1; unfold bellShift bellB at h1
  (split_ifs at h1; omega)

theorem bellG_eq (hd : d.Valid) : bellG d = layerMat
    ([Instr.cnot (sw d ⟨d.out, out_lt_W hd⟩) (wB d) (sw_out_ne_wB hd)] ++
      swapsUpTo (d := d) d.totalWires) := by
  have ho := hd.out_lt
  have hw := priv_le_totalWires d
  rw [bellG, List.filterMap_append, swapsUpTo]
  congr 2
  have h1 : bellShift d d.out < (bellDesc d).totalWires := bellShift_lt (by omega)
  have h2 : bellB d < (bellDesc d).totalWires := (wB d).2
  have h3 : bellShift d d.out ≠ bellB d := by unfold bellShift bellB; (split_ifs; omega)
  simp [Gate.toInstr?, h1, h2, h3]
  exact ⟨rfl, rfl⟩

/-- **The copy-and-ship layer on basis labels.** -/
theorem bellG_mulVec (hd : d.Valid) (v : QState (bellDesc d).totalWires)
    (y : Qubits (bellDesc d).totalWires) :
    (bellG d *ᵥ v) y = v (cnotFun (sw d ⟨d.out, out_lt_W hd⟩) (wB d) (y ∘ σ d d.totalWires)) := by
  rw [bellG_eq hd, layerMat_mulVec, List.singleton_append, runLayer_cons,
    runLayer_swapsUpTo _ le_rfl]
  rfl

end ShiQIP
