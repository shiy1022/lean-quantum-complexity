/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The generic one-label transfer loop (plan task S08).
-/
import Machine.Host

set_option autoImplicit false

/-!
# Transfer loops

`loopStmt src ts self next` pops the wrapper register `src`; if a bit `b` was present it pushes
`b` (rendered by each target's function) onto every target in `ts`, in order, and repeats;
when `src` is empty it moves to `next`. One iteration is one machine step.

Copy, reversal, restore, clear, unary-length and checker-input preparation are all instances:
clearing has no targets; moving has one; copying has two. Targets must differ from `src`.

The loop is proved against **any** host program `M` containing the statement at label `self`.
Its exact result is `loopOut`, and its peak space is the larger of the entry and exit spaces:
space changes by the same amount `ts.length - 1` at every iteration.
-/

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

variable {κ : Type} [DecidableEq κ] {Γ : κ → Type} {σ L : Type}

/-- Host stack assignments. -/
abbrev Stacks (Γ : κ → Type) := ∀ i, List (HG Γ i)

/-- A push target: a host stack and a rendering of bits as its symbols. -/
abbrev Tgt (Γ : κ → Type) := Σ i : κ ⊕ Ext, (Bool → HG Γ i)

/-- Push the register bit onto each target, then continue with `q`. -/
def pushes : List (Tgt Γ) → Stmt (HG Γ) L (σ × Reg) → Stmt (HG Γ) L (σ × Reg)
  | [], q => q
  | t :: ts, q => .push t.1 (fun v => t.2 v.2.1) (pushes ts q)

/-- The stack effect of `pushes`. -/
def pushAll : List (Tgt Γ) → Bool → Stacks Γ → Stacks Γ
  | [], _, S => S
  | t :: ts, b, S => pushAll ts b (Function.update S t.1 (t.2 b :: S t.1))

theorem stepAux_pushes (ts : List (Tgt Γ)) (q : Stmt (HG Γ) L (σ × Reg)) (v : σ × Reg)
    (S : Stacks Γ) : stepAux (pushes ts q) v S = stepAux q v (pushAll ts v.2.1 S) := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih => exact ih _

/-- Pop wrapper register `src`, recording the bit and whether one was present. -/
def popBit (src : Ext) (q : Stmt (HG Γ) L (σ × Reg)) : Stmt (HG Γ) L (σ × Reg) :=
  .pop (.inr src) (fun v (o : Option Bool) => (v.1, (o.getD false, o.isSome))) q

/-- The transfer loop at label `self`, exiting to `next`. -/
def loopStmt (src : Ext) (ts : List (Tgt Γ)) (self next : L) : Stmt (HG Γ) L (σ × Reg) :=
  popBit src (.branch (fun v => v.2.2) (pushes ts (.goto fun _ => self)) (.goto fun _ => next))

/-- Targets avoid the source register. -/
def Avoids (ts : List (Tgt Γ)) (j : κ ⊕ Ext) : Prop := ∀ t ∈ ts, t.1 ≠ j

theorem pushAll_apply_ne {ts : List (Tgt Γ)} {j : κ ⊕ Ext} (h : Avoids ts j) (b : Bool)
    (S : Stacks Γ) : pushAll ts b S j = S j := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih =>
      simp only [pushAll]
      rw [ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]
      exact Function.update_of_ne (Ne.symm (h t List.mem_cons_self)) _ _

theorem pushAll_update {ts : List (Tgt Γ)} {j : κ ⊕ Ext} (h : Avoids ts j) (b : Bool)
    (S : Stacks Γ) (x : List (HG Γ j)) :
    pushAll ts b (Function.update S j x) = Function.update (pushAll ts b S) j x := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih =>
      have hne : t.1 ≠ j := h t List.mem_cons_self
      simp only [pushAll]
      rw [Function.update_of_ne hne, Function.update_comm (Ne.symm hne),
        ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

/-- The stacks after the loop drains `src` holding `w`. -/
def loopOut (ts : List (Tgt Γ)) (src : Ext) (w : List Bool) (S : Stacks Γ) : Stacks Γ :=
  w.foldl (fun S b => pushAll ts b S) (Function.update S (.inr src) [])

theorem loopOut_nil (ts : List (Tgt Γ)) (src : Ext) (S : Stacks Γ) (h : S (.inr src) = []) :
    loopOut ts src [] S = S := by
  simp only [loopOut, List.foldl_nil]
  exact Function.update_eq_self_iff.mpr h.symm

theorem loopOut_cons {ts : List (Tgt Γ)} {src : Ext} (hts : Avoids ts (.inr src)) (b : Bool)
    (w : List Bool) (S : Stacks Γ) :
    loopOut ts src (b :: w) S =
      loopOut ts src w (pushAll ts b (Function.update S (.inr src) w)) := by
  simp only [loopOut, List.foldl_cons]
  congr 1
  rw [pushAll_update hts, pushAll_update hts, Function.update_idem]

theorem foldl_pushAll_apply_ne {ts : List (Tgt Γ)} {j : κ ⊕ Ext} (hj : Avoids ts j)
    (w : List Bool) (S : Stacks Γ) : w.foldl (fun S b => pushAll ts b S) S j = S j := by
  induction w generalizing S with
  | nil => rfl
  | cons b w ih => rw [List.foldl_cons, ih, pushAll_apply_ne hj]

theorem loopOut_apply_ne {ts : List (Tgt Γ)} {src : Ext} (j : κ ⊕ Ext) (hj : Avoids ts j)
    (hjs : j ≠ .inr src) (w : List Bool) (S : Stacks Γ) : loopOut ts src w S j = S j := by
  unfold loopOut
  rw [foldl_pushAll_apply_ne hj]
  exact Function.update_of_ne hjs _ _

theorem loopOut_src {ts : List (Tgt Γ)} {src : Ext} (hts : Avoids ts (.inr src))
    (w : List Bool) (S : Stacks Γ) : loopOut ts src w S (.inr src) = [] := by
  unfold loopOut
  rw [foldl_pushAll_apply_ne hts]
  exact Function.update_self _ _ _

/-! ### Steps and runs -/

local notation "run" => ShiTMSubroutine.run

variable (M : L → Stmt (HG Γ) L (σ × Reg)) (src : Ext) (ts : List (Tgt Γ)) (lp next : L)

theorem step_loop_cons (hM : M lp = loopStmt src ts lp next) (v : σ × Reg) (S : Stacks Γ)
    (b : Bool) (w : List Bool) (hS : S (.inr src) = b :: w) :
    step M ⟨some lp, v, S⟩ =
      some ⟨some lp, (v.1, (b, true)), pushAll ts b (Function.update S (.inr src) w)⟩ := by
  simp only [step, hM, loopStmt, popBit, stepAux]
  rw [stepAux_pushes]
  simp [hS, stepAux]

theorem step_loop_nil (hM : M lp = loopStmt src ts lp next) (v : σ × Reg) (S : Stacks Γ)
    (hS : S (.inr src) = []) :
    step M ⟨some lp, v, S⟩ = some ⟨some next, (v.1, (false, false)), S⟩ := by
  simp only [step, hM, loopStmt, popBit, stepAux]
  simp [hS]

/-- **Loop run.** Draining `w` takes `w.length + 1` steps, ends at `next` with a clean
register, and leaves exactly `loopOut`. The entry register is arbitrary. -/
theorem loop_run (hM : M lp = loopStmt src ts lp next) (hts : Avoids ts (.inr src))
    (w : List Bool) (s : σ) (r : Reg) (S : Stacks Γ) (hS : S (.inr src) = w) :
    (run M)^[w.length + 1] (some ⟨some lp, (s, r), S⟩) =
      some ⟨some next, (s, (false, false)), loopOut ts src w S⟩ := by
  induction w generalizing S r with
  | nil =>
      rw [loopOut_nil ts src S hS]
      exact step_loop_nil M src ts lp next hM (s, r) S hS
  | cons b w ih =>
      rw [List.length_cons, iterate_run_succ, step_loop_cons M src ts lp next hM (s, r) S b w hS,
        loopOut_cons hts]
      apply ih
      rw [pushAll_apply_ne hts]
      exact Function.update_self _ _ _

/-! ### Space -/

variable [Fintype κ]

theorem size_pushAll (ts : List (Tgt Γ)) (b : Bool) (S : Stacks Γ) :
    ShiTMStackGrowth.size (pushAll ts b S) = ShiTMStackGrowth.size S + ts.length := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih =>
      simp only [pushAll, List.length_cons]
      rw [ih, size_update_cons]
      omega

omit [DecidableEq κ] [Fintype κ] in
theorem mul_ge_aux (n a : ℕ) (ha : 1 ≤ a) : n + a ≤ (n + 1) * a := by
  have := Nat.le_mul_of_pos_right n ha
  rw [Nat.succ_mul]
  omega

theorem size_loopOut {ts : List (Tgt Γ)} {src : Ext} (hts : Avoids ts (.inr src))
    (w : List Bool) (S : Stacks Γ) (hS : S (.inr src) = w) :
    ShiTMStackGrowth.size (loopOut ts src w S) + w.length =
      ShiTMStackGrowth.size S + w.length * ts.length := by
  induction w generalizing S with
  | nil => simp [loopOut_nil ts src S hS]
  | cons b w ih =>
      rw [loopOut_cons hts]
      have h1 := ih (pushAll ts b (Function.update S (.inr src) w))
        (by rw [pushAll_apply_ne hts]; exact Function.update_self _ _ _)
      have h2 := size_pushAll ts b (Function.update S (.inr src) w)
      have h3 := size_update_tail S (.inr src) b w hS
      simp only [List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- **Loop segment.** Every configuration of the loop is within the larger of the entry and
exit spaces. -/
theorem loop_seg (hM : M lp = loopStmt src ts lp next) (hts : Avoids ts (.inr src))
    (w : List Bool) (s : σ) (r : Reg) (S : Stacks Γ) (hS : S (.inr src) = w) :
    Seg M ⟨some lp, (s, r), S⟩ (w.length + 1) ⟨some next, (s, (false, false)), loopOut ts src w S⟩
      (max (ShiTMStackGrowth.size S) (ShiTMStackGrowth.size (loopOut ts src w S))) := by
  induction w generalizing S r with
  | nil =>
      rw [loopOut_nil ts src S hS]
      exact (Seg.single (step_loop_nil M src ts lp next hM (s, r) S hS) le_rfl le_rfl).mono
        (le_max_left _ _)
  | cons b w ih =>
      rw [loopOut_cons hts, List.length_cons]
      set S₁ := pushAll ts b (Function.update S (.inr src) w) with hS₁def
      have hS₁ : S₁ (.inr src) = w := by
        rw [hS₁def, pushAll_apply_ne hts]; exact Function.update_self _ _ _
      have h1 : Seg M ⟨some lp, (s, r), S⟩ 1 ⟨some lp, (s, (b, true)), S₁⟩
          (max (ShiTMStackGrowth.size S) (ShiTMStackGrowth.size S₁)) :=
        Seg.single (step_loop_cons M src ts lp next hM (s, r) S b w hS)
          (le_max_left _ _) (le_max_right _ _)
      have h := Seg.trans h1 (ih (b, true) S₁ hS₁)
      -- the intermediate space lies between the entry and exit spaces
      have hmid : ShiTMStackGrowth.size S₁ ≤
          max (ShiTMStackGrowth.size S) (ShiTMStackGrowth.size (loopOut ts src w S₁)) := by
        have e1 := size_pushAll ts b (Function.update S (.inr src) w)
        have e2 := size_update_tail S (.inr src) b w hS
        have e3 := size_loopOut hts w S₁ hS₁
        rw [← hS₁def] at e1
        rcases Nat.eq_zero_or_pos ts.length with h0 | hpos
        · exact le_max_of_le_left (by omega)
        · have e4 := mul_ge_aux w.length ts.length hpos
          refine le_max_of_le_right ?_
          rw [Nat.succ_mul] at e4
          omega
      exact h.mono (max_le (max_le (le_max_left _ _) hmid) (max_le hmid (le_max_right _ _)))

end ShiPPPSPACE
