/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The binary increment machine (plan task S07).
-/
import Machine.Loop
import Count.FixedBits

set_option autoImplicit false

/-!
# Ripple-carry increment on a wrapper register

Label `incL` pops the register `A` (least significant bit on top). A popped `true` becomes a
carry: a `false` is parked on scratch register `T` and the loop repeats. A popped `false` is
replaced by `true` and control moves to `moveNo`; an empty register means overflow and control
moves to `moveOv`. Both move labels are transfer loops returning the parked `false`s from `T`
to `A`, then exiting to `nextNo` / `nextOv`.

Result: `A` holds `(inc w).1`, `T` is empty, the exit records `(inc w).2`, and every
configuration uses exactly the entry space (each statement pops and pushes at most once each).
-/

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

variable {κ : Type} [DecidableEq κ] {Γ : κ → Type} {σ L : Type}

local notation "run" => ShiTMSubroutine.run

/-- The carry-propagation statement. -/
def incStmt (A T : Ext) (self moveNo moveOv : L) : Stmt (HG Γ) L (σ × Reg) :=
  popBit A (.branch (fun v => v.2.2)
    (.branch (fun v => v.2.1)
      (.push (.inr T) (fun _ => false) (.goto fun _ => self))
      (.push (.inr A) (fun _ => true) (.goto fun _ => moveNo)))
    (.goto fun _ => moveOv))

/-- Move target: push each bit unchanged onto register `A`. -/
def moveTgt (A : Ext) : List (Tgt Γ) := [⟨.inr A, id⟩]

omit [DecidableEq κ] in
theorem avoids_moveTgt {A T : Ext} (h : A ≠ T) : Avoids (moveTgt (Γ := Γ) A) (.inr T) := by
  intro t ht
  simp only [moveTgt, List.mem_singleton] at ht
  subst ht
  simpa using h

/-- Pointwise effect of a single-target loop on its target. -/
theorem foldl_single_apply (i : κ ⊕ Ext) (f : Bool → HG Γ i) (w : List Bool) (S : Stacks Γ) :
    w.foldl (fun S b => pushAll [⟨i, f⟩] b S) S i = (w.map f).reverse ++ S i := by
  induction w generalizing S with
  | nil => rfl
  | cons b w ih =>
      rw [List.foldl_cons, ih]
      simp [pushAll]

theorem loopOut_single_apply (i : κ ⊕ Ext) (f : Bool → HG Γ i) (src : Ext) (h : i ≠ .inr src)
    (w : List Bool) (S : Stacks Γ) :
    loopOut [⟨i, f⟩] src w S i = (w.map f).reverse ++ S i := by
  unfold loopOut
  rw [foldl_single_apply, Function.update_of_ne h]

/-- Number of steps of the increment, with `j` falses already parked. -/
def incSteps : List Bool → ℕ → ℕ
  | true :: w, j => incSteps w (j + 1) + 1
  | _, j => j + 2

variable (M : L → Stmt (HG Γ) L (σ × Reg)) (A T : Ext) (incL moveNo moveOv nextNo nextOv : L)

/-- The labels of one increment routine inside a host program. -/
structure IncAt : Prop where
  ne : A ≠ T
  hinc : M incL = incStmt A T incL moveNo moveOv
  hno : M moveNo = loopStmt T (moveTgt A) moveNo nextNo
  hov : M moveOv = loopStmt T (moveTgt A) moveOv nextOv

variable {M A T incL moveNo moveOv nextNo nextOv}

/-- The stacks produced by the increment. -/
def incOut (A T : Ext) (j : ℕ) (w : List Bool) (S : Stacks Γ) : Stacks Γ :=
  Function.update (Function.update S (.inr T) []) (.inr A) (List.replicate j false ++ (inc w).1)

theorem incOut_apply_ne (j : ℕ) (w : List Bool) (S : Stacks Γ) (i : κ ⊕ Ext)
    (hA : i ≠ .inr A) (hT : i ≠ .inr T) : incOut A T j w S i = S i := by
  unfold incOut
  rw [Function.update_of_ne hA, Function.update_of_ne hT]

theorem size_incOut (h : A ≠ T) [Fintype κ] (j : ℕ) (w : List Bool) (S : Stacks Γ)
    (hA : S (.inr A) = w) (hT : S (.inr T) = List.replicate j false) :
    ShiTMStackGrowth.size (incOut A T j w S) = ShiTMStackGrowth.size S := by
  have h1 := size_update S (.inr T) []
  have h2 := size_update (Function.update S (.inr T) []) (.inr A)
    (List.replicate j false ++ (inc w).1)
  rw [Function.update_of_ne (by simpa using h)] at h2
  simp only [hT, hA, List.length_nil, List.length_replicate, List.length_append,
    length_inc] at h1 h2
  unfold incOut
  omega

theorem step_inc_true (H : IncAt M A T incL moveNo moveOv nextNo nextOv) (v : σ × Reg)
    (S : Stacks Γ) (w : List Bool) (hS : S (.inr A) = true :: w) :
    step M ⟨some incL, v, S⟩ = some ⟨some incL, (v.1, (true, true)),
      Function.update (Function.update S (.inr A) w) (.inr T) (false :: S (.inr T))⟩ := by
  have hne : (Sum.inr T : κ ⊕ Ext) ≠ .inr A := by simpa using H.ne.symm
  simp [step, H.hinc, incStmt, popBit, stepAux, hS, Function.update_of_ne hne]

theorem step_inc_false (H : IncAt M A T incL moveNo moveOv nextNo nextOv) (v : σ × Reg)
    (S : Stacks Γ) (w : List Bool) (hS : S (.inr A) = false :: w) :
    step M ⟨some incL, v, S⟩ = some ⟨some moveNo, (v.1, (false, true)),
      Function.update S (.inr A) (true :: w)⟩ := by
  simp [step, H.hinc, incStmt, popBit, stepAux, hS]

theorem step_inc_nil (H : IncAt M A T incL moveNo moveOv nextNo nextOv) (v : σ × Reg)
    (S : Stacks Γ) (hS : S (.inr A) = []) :
    step M ⟨some incL, v, S⟩ = some ⟨some moveOv, (v.1, (false, false)), S⟩ := by
  have : Function.update S (.inr A) [] = S := Function.update_eq_self_iff.mpr hS.symm
  simp [step, H.hinc, incStmt, popBit, stepAux, hS]

variable [Fintype κ]

/-- **Increment.** Exact run and constant peak space. -/
theorem inc_seg (H : IncAt M A T incL moveNo moveOv nextNo nextOv) (w : List Bool) (j : ℕ)
    (s : σ) (r : Reg) (S : Stacks Γ) (hA : S (.inr A) = w)
    (hT : S (.inr T) = List.replicate j false) :
    Seg M ⟨some incL, (s, r), S⟩ (incSteps w j)
      ⟨some (if (inc w).2 then nextOv else nextNo), (s, (false, false)), incOut A T j w S⟩
      (ShiTMStackGrowth.size S) := by
  have hTA : (Sum.inr T : κ ⊕ Ext) ≠ .inr A := by simpa using H.ne.symm
  have hAT : (Sum.inr A : κ ⊕ Ext) ≠ .inr T := by simpa using H.ne
  -- the closing move loop, from any parked count
  have hmove : ∀ (j : ℕ) (lbl nxt : L), M lbl = loopStmt T (moveTgt A) lbl nxt →
      ∀ (S' : Stacks Γ) (r' : Reg) (u : List Bool), S' (.inr T) = List.replicate j false →
      S' (.inr A) = u →
      Seg M ⟨some lbl, (s, r'), S'⟩ (j + 1) ⟨some nxt, (s, (false, false)),
        Function.update (Function.update S' (.inr T) []) (.inr A)
          (List.replicate j false ++ u)⟩ (ShiTMStackGrowth.size S') := by
    intro j lbl nxt hM S' r' u hT' hA'
    have hseg := loop_seg M T (moveTgt A) lbl nxt hM (avoids_moveTgt H.ne)
      (List.replicate j false) s r' S' hT'
    have hlen := size_loopOut (avoids_moveTgt H.ne) (List.replicate j false) S' hT'
    have hout : loopOut (moveTgt A) T (List.replicate j false) S' =
        Function.update (Function.update S' (.inr T) []) (.inr A)
          (List.replicate j false ++ u) := by
      funext i
      by_cases hi : i = .inr A
      · subst hi
        rw [Function.update_self]
        have := loopOut_single_apply (Γ := Γ) (.inr A) id T hAT (List.replicate j false) S'
        simpa [moveTgt, hA'] using this
      · by_cases hi' : i = .inr T
        · subst hi'
          rw [Function.update_of_ne hi, Function.update_self]
          exact loopOut_src (avoids_moveTgt H.ne) _ _
        · rw [Function.update_of_ne hi, Function.update_of_ne hi']
          exact loopOut_apply_ne i (by
            intro t ht; simp only [moveTgt, List.mem_singleton] at ht; subst ht
            exact Ne.symm hi) hi' _ _
    rw [List.length_replicate] at hseg
    rw [hout] at hseg hlen
    simp only [moveTgt, List.length_replicate, List.length_singleton, Nat.mul_one] at hlen
    refine hseg.mono (max_le le_rfl (by omega))
  induction w generalizing j S r with
  | nil =>
      have h1 := Seg.single (B := ShiTMStackGrowth.size S)
        (step_inc_nil H (s, r) S hA) le_rfl le_rfl
      have h2 := hmove j moveOv nextOv H.hov S (false, false) [] hT hA
      have h := Seg.trans' h1 h2
      rw [show j + 1 + 1 = incSteps [] j from rfl] at h
      simpa [inc, incOut] using h
  | cons b w ih =>
      cases b with
      | false =>
          have h1 := Seg.single (B := ShiTMStackGrowth.size S)
            (step_inc_false H (s, r) S w hA) le_rfl (by
              show ShiTMStackGrowth.size (Function.update S (.inr A) (true :: w)) ≤ _
              have := size_update S (.inr A) (true :: w)
              rw [hA] at this; simp at this; omega)
          have h2 := hmove j moveNo nextNo H.hno (Function.update S (.inr A) (true :: w))
            (false, true) (true :: w) (by rw [Function.update_of_ne hTA]; exact hT)
            (Function.update_self _ _ _)
          have hsz : ShiTMStackGrowth.size (Function.update S (.inr A) (true :: w)) =
              ShiTMStackGrowth.size S := by
            have := size_update S (.inr A) (true :: w)
            rw [hA] at this; simp at this; omega
          rw [hsz] at h2
          have h := Seg.trans' h1 h2
          have hout : Function.update (Function.update (Function.update S (.inr A) (true :: w))
              (.inr T) []) (.inr A) (List.replicate j false ++ true :: w) = incOut A T j (false :: w) S := by
            unfold incOut
            rw [Function.update_comm hAT, Function.update_idem]
            simp [inc]
          rw [hout, show j + 1 + 1 = incSteps (false :: w) j from rfl] at h
          simpa [inc] using h
      | true =>
          set S₁ := Function.update (Function.update S (.inr A) w) (.inr T) (false :: S (.inr T))
            with hS₁
          have hsz₁ : ShiTMStackGrowth.size S₁ = ShiTMStackGrowth.size S := by
            have e1 := size_update_tail S (.inr A) true w hA
            have e2 := size_update_cons (Function.update S (.inr A) w) (.inr T) false
            rw [Function.update_of_ne hTA] at e2
            rw [hS₁]; omega
          have h1 := Seg.single (B := ShiTMStackGrowth.size S)
            (step_inc_true H (s, r) S w hA) le_rfl (le_of_eq hsz₁)
          have h2 := ih (j + 1) (true, true) S₁
            (by rw [hS₁, Function.update_of_ne hAT]; exact Function.update_self _ _ _)
            (by rw [hS₁, Function.update_self, hT, List.replicate_succ])
          rw [hsz₁] at h2
          have h := Seg.trans' h1 h2
          have hout : incOut A T (j + 1) w S₁ = incOut A T j (true :: w) S := by
            unfold incOut
            funext i
            by_cases hi : i = .inr A
            · subst hi
              simp only [Function.update_self, inc]
              rw [List.replicate_succ', List.append_assoc, List.singleton_append]
            · rw [Function.update_of_ne hi, Function.update_of_ne hi]
              by_cases hi' : i = .inr T
              · subst hi'; simp
              · rw [Function.update_of_ne hi', Function.update_of_ne hi', hS₁,
                  Function.update_of_ne hi', Function.update_of_ne hi]
          rw [hout, show incSteps w (j + 1) + 1 = incSteps (true :: w) j from rfl] at h
          rw [show (inc (true :: w)).2 = (inc w).2 from rfl]
          exact h

end ShiPPPSPACE
