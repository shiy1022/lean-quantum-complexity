/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Frame properties: stacks outside a statement's write set are preserved (plan task S02).
-/
import Space.Run

set_option autoImplicit false

namespace ShiSpace

open Turing Turing.TM2

variable {K L V : Type} [DecidableEq K] {G : K → Type}

local notation "run" => ShiTMSubroutine.run

/-- Whether a statement contains a push or pop on stack `j`. Peeks only read. -/
def writes (j : K) : Stmt G L V → Bool
  | .push k _ q => decide (k = j) || writes j q
  | .peek _ _ q => writes j q
  | .pop k _ q => decide (k = j) || writes j q
  | .load _ q => writes j q
  | .branch _ p q => writes j p || writes j q
  | .goto _ => false
  | .halt => false

theorem stepAux_stk_of_not_writes (j : K) (q : Stmt G L V) (hq : writes j q = false)
    (v : V) (S : ∀ k, List (G k)) : (stepAux q v S).stk j = S j := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hq
      change (stepAux q v (Function.update S k (f v :: S k))).stk j = S j
      rw [ih hq.2, Function.update_of_ne (Ne.symm hq.1)]
  | peek k f q ih => exact ih hq _ _
  | pop k f q ih =>
      simp only [writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hq
      change (stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk j = S j
      rw [ih hq.2, Function.update_of_ne (Ne.symm hq.1)]
  | load f q ih => exact ih hq _ _
  | branch f p q ihp ihq =>
      simp only [writes, Bool.or_eq_false_iff] at hq
      simp only [stepAux]
      cases f v
      · exact ihq hq.2 v S
      · exact ihp hq.1 v S
  | goto f => rfl
  | halt => rfl

/-- A program that never writes stack `j` preserves it along every run. -/
theorem iterate_stk_of_not_writes (M : L → Stmt G L V) (j : K)
    (hM : ∀ l, writes j (M l) = false) (n : ℕ) (c d : Cfg G L V)
    (h : (run M)^[n] (some c) = some d) : d.stk j = c.stk j := by
  induction n generalizing d with
  | zero => cases h; rfl
  | succ n ih =>
      rw [iterate_run_succ'] at h
      cases he : (run M)^[n] (some c) with
      | none => rw [he] at h; cases h
      | some e =>
          rw [he] at h
          rcases e with ⟨l, v, S⟩
          cases l with
          | none => cases h
          | some l =>
              cases h
              have := stepAux_stk_of_not_writes j (M l) (hM l) v S
              rw [this]
              exact ih _ he

/-! ### Splitting space into an active region and a frame -/

variable [Fintype K]

/-- Total length of the stacks in `A`. -/
def sizeOn (A : Finset K) (S : ∀ k, List (G k)) : ℕ := ∑ k ∈ A, (S k).length

theorem size_eq_sizeOn_add (A : Finset K) (S : ∀ k, List (G k)) :
    ShiTMStackGrowth.size S = sizeOn A S + sizeOn Aᶜ S := by
  unfold ShiTMStackGrowth.size sizeOn
  exact (Finset.sum_add_sum_compl A _).symm

omit [DecidableEq K] [Fintype K] in
theorem sizeOn_congr (A : Finset K) (S T : ∀ k, List (G k)) (h : ∀ k ∈ A, S k = T k) :
    sizeOn A S = sizeOn A T :=
  Finset.sum_congr rfl fun k hk => by rw [h k hk]

/-- A program writing only stacks in `A` leaves the frame's space unchanged; the total space
of a reached configuration is its active space plus the original frame space. -/
theorem size_iterate_of_frame (M : L → Stmt G L V) (A : Finset K)
    (hM : ∀ j ∉ A, ∀ l, writes j (M l) = false) (n : ℕ) (c d : Cfg G L V)
    (h : (run M)^[n] (some c) = some d) :
    ShiTMStackGrowth.size d.stk = sizeOn A d.stk + sizeOn Aᶜ c.stk := by
  rw [size_eq_sizeOn_add A d.stk]
  congr 1
  apply sizeOn_congr
  intro k hk
  exact iterate_stk_of_not_writes M k (hM k (Finset.mem_compl.mp hk)) n c d h

end ShiSpace
