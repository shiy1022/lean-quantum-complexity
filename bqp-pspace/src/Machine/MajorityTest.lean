/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The strict-majority test `2 * a > 2^m` as a finite-state scan (plan task S11).
-/
import Machine.Loop
import Count.FixedBits

set_option autoImplicit false

/-!
# Strict majority by one scan of the counter

For a little-endian counter `l` of width `m+1` with value `a`, `2 * a > 2^m` holds exactly when
the top bit is set, or the next bit is set and some lower bit is set. A left-to-right scan
keeping `(any, prev, cur)` — the OR of all bits before the last two, the second-to-last bit, and
the last bit — decides it with finite control. At `m = 0` the answer is the single bit. Ties
are rejected. The threshold is never materialised, and nothing unary is built.
-/

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

/-- Scan state `(any, prev, cur)`. -/
abbrev ScanSt := Bool × Bool × Bool

def scanStep (st : ScanSt) (b : Bool) : ScanSt := (st.1 || st.2.1, st.2.2, b)

def scanAll (st : ScanSt) (l : List Bool) : ScanSt := l.foldl scanStep st

def answer (st : ScanSt) : Bool := st.2.2 || (st.2.1 && st.1)

theorem scanAll_cons (st : ScanSt) (b : Bool) (l : List Bool) :
    scanAll st (b :: l) = scanAll (scanStep st b) l := rfl

theorem scanAll_append (st : ScanSt) (u v : List Bool) :
    scanAll st (u ++ v) = scanAll (scanAll st u) v := List.foldl_append

theorem scanAll_or (st : ScanSt) (l : List Bool) :
    ((scanAll st l).1 || (scanAll st l).2.1 || (scanAll st l).2.2) =
      (st.1 || st.2.1 || st.2.2 || l.any id) := by
  induction l generalizing st with
  | nil => simp [scanAll]
  | cons b l ih =>
      rw [scanAll_cons, ih]
      rcases st with ⟨a, p, c⟩
      cases a <;> cases p <;> cases c <;> cases b <;> simp [scanStep]

theorem val_append (u v : List Bool) : val (u ++ v) = val u + 2 ^ u.length * val v := by
  induction u with
  | nil => simp
  | cons b u ih =>
      simp only [List.cons_append, val_cons, ih, List.length_cons, pow_succ]
      ring

theorem val_pos_iff (l : List Bool) : 0 < val l ↔ l.any id = true := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [ih]

/-- **Correctness of the scan.** -/
theorem answer_scanAll (m : ℕ) (l : List Bool) (hl : l.length = m + 1) :
    answer (scanAll (false, false, false) l) = decide (2 * val l > 2 ^ m) := by
  rcases m with _ | m
  · match l, hl with
    | [q], _ => cases q <;> decide
  · -- split off the top two bits
    have hd : (l.drop m).length = 2 := by simp; omega
    obtain ⟨p, q, hpq⟩ : ∃ p q, l.drop m = [p, q] := by
      match h : l.drop m, hd with
      | [p, q], _ => exact ⟨p, q, rfl⟩
    have hlow : (l.take m).length = m := by simp; omega
    have hl' : l = l.take m ++ [p, q] := by rw [← hpq, List.take_append_drop]
    set low := l.take m
    rw [hl']
    have hs : scanAll (false, false, false) (low ++ [p, q]) =
        ((scanAll (false, false, false) low).1 || (scanAll (false, false, false) low).2.1 ||
          (scanAll (false, false, false) low).2.2, p, q) := by
      rw [scanAll_append]
      simp [scanAll, scanStep, Bool.or_assoc]
    have hor := scanAll_or (false, false, false) low
    simp only [Bool.or_false, Bool.false_or] at hor
    rw [hs, hor]
    have hv := val_append low [p, q]
    have hlt := val_lt low
    have hpos := val_pos_iff low
    rw [hlow] at hv hlt
    rw [hv, show 2 ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff]
    cases p <;> cases q <;> simp only [answer, val_cons, val_nil, Bool.toNat_false,
      Bool.toNat_true, Bool.or_false, Bool.true_and, Bool.false_and] <;>
      constructor <;> intro h
    · simp at h
    · omega
    · omega
    · trivial
    · have := hpos.mpr h; omega
    · exact hpos.mp (by omega)
    · omega
    · trivial

/-! ### The scan machine -/

variable {κ : Type} [DecidableEq κ] {Γ : κ → Type} {σ L : Type}

local notation "run" => ShiTMSubroutine.run

/-- Label `scanL st` pops the counter `C` and moves to `scanL (scanStep st b)`; when `C` is
empty it pushes `answer st` onto `O` and moves to `next`. -/
def scanStmt (C O : Ext) (scanL : ScanSt → L) (next : L) (st : ScanSt) :
    Stmt (HG Γ) L (σ × Reg) :=
  popBit C (.branch (fun v => v.2.2) (.goto fun v => scanL (scanStep st v.2.1))
    (.push (.inr O) (fun _ => answer st) (.goto fun _ => next)))

variable (M : L → Stmt (HG Γ) L (σ × Reg)) (C O : Ext) (scanL : ScanSt → L) (next : L)

/-- The stacks after scanning `l` from state `st`. -/
def scanOut (C O : Ext) (st : ScanSt) (l : List Bool) (S : Stacks Γ) : Stacks Γ :=
  Function.update (Function.update S (.inr C) []) (.inr O) (answer (scanAll st l) :: S (.inr O))

variable [Fintype κ]

/-- **Scan run and space.** `l.length + 1` steps; peak at most entry space plus one. -/
theorem scan_seg (hCO : C ≠ O) (hM : ∀ st, M (scanL st) = scanStmt C O scanL next st)
    (l : List Bool) (st : ScanSt) (s : σ) (r : Reg) (S : Stacks Γ) (hS : S (.inr C) = l) :
    Seg M ⟨some (scanL st), (s, r), S⟩ (l.length + 1)
      ⟨some next, (s, (false, false)), scanOut C O st l S⟩ (ShiTMStackGrowth.size S + 1) := by
  have hOC : (Sum.inr O : κ ⊕ Ext) ≠ .inr C := by simpa using hCO.symm
  induction l generalizing st S r with
  | nil =>
      have h0 : Function.update S (.inr C) [] = S := Function.update_eq_self_iff.mpr hS.symm
      have hout : scanOut C O st [] S = Function.update S (.inr O) (answer st :: S (.inr O)) := by
        unfold scanOut; rw [h0]; rfl
      have hstep : step M ⟨some (scanL st), (s, r), S⟩ =
          some ⟨some next, (s, (false, false)), scanOut C O st [] S⟩ := by
        rw [hout]
        simp only [step, hM, scanStmt, popBit, stepAux, hS, List.head?_nil, List.tail_nil, h0]
        rfl
      refine Seg.single hstep (Nat.le_succ _) ?_
      show ShiTMStackGrowth.size (scanOut C O st [] S) ≤ _
      rw [hout, size_update_cons]
  | cons b l ih =>
      have hstep : step M ⟨some (scanL st), (s, r), S⟩ =
          some ⟨some (scanL (scanStep st b)), (s, (b, true)), Function.update S (.inr C) l⟩ := by
        simp [step, hM, scanStmt, popBit, stepAux, hS]
      have hsz := size_update_tail S (.inr C) b l hS
      have h1 := Seg.single (B := ShiTMStackGrowth.size S + 1) hstep (Nat.le_succ _)
        (by show ShiTMStackGrowth.size (Function.update S (.inr C) l) ≤ _; omega)
      have h2 := ih (scanStep st b) (b, true) (Function.update S (.inr C) l)
        (Function.update_self _ _ _)
      have hout : scanOut C O (scanStep st b) l (Function.update S (.inr C) l) =
          scanOut C O st (b :: l) S := by
        unfold scanOut
        rw [Function.update_idem, Function.update_of_ne hOC, scanAll_cons]
      rw [hout] at h2
      have h := Seg.trans' h1 (h2.mono (by omega))
      rwa [List.length_cons]

end ShiPPPSPACE
