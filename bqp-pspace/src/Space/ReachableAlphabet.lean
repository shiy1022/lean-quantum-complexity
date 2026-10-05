/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Reachable stack alphabets and statement-internal peaks (plan task S03).
-/
import Space.PeakComposition
import «AMPUNI-finite-stack-growth»

set_option autoImplicit false

/-!
# Stack cells carry bounded information

`FinTM2` only requires the *input* alphabet to be finite; other stack types `tm.Γ j` may be
infinite. Nevertheless, every symbol that can appear on any stack during a run from an input
configuration is either an input symbol (on stack `k₀`) or the value of one of the finitely
many push expressions `f v`, for a finite program label and a finite internal state `v`.
Peeks and pops change only the finite control. Hence each stack ranges over a fixed finite
alphabet, and stack height measures information up to a machine-dependent constant factor.

We also bound the transient space *inside* one statement: a statement is a finite tree of
primitive operations, and its intermediate stack contents never exceed the boundary space by
more than `pushBudget`, a machine-dependent constant (`ShiTMStackGrowth.finite_growth`). The
space model of `Space/Model.lean` measures statement boundaries; the two measures therefore
differ by at most that constant.
-/

namespace ShiSpace

open Turing Turing.TM2

section Generic

variable {K L V : Type} [DecidableEq K] {G : K → Type}

local notation "run" => ShiTMSubroutine.run

/-- The tagged symbols a statement may push, over all internal states. -/
def pushed : Stmt G L V → Set (Σ k, G k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, G k)) ∪ pushed q
  | .peek _ _ q => pushed q
  | .pop _ _ q => pushed q
  | .load _ q => pushed q
  | .branch _ p q => pushed p ∪ pushed q
  | .goto _ => ∅
  | .halt => ∅

omit [DecidableEq K] in
theorem pushed_finite [Finite V] (q : Stmt G L V) : (pushed q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ p q ihp ihq => exact ihp.union ihq
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

/-- Every symbol on every stack belongs to `R`. -/
def SymsIn (R : Set (Σ k, G k)) (S : ∀ k, List (G k)) : Prop :=
  ∀ k, ∀ a ∈ S k, (⟨k, a⟩ : Σ k, G k) ∈ R

theorem symsIn_update_cons {R : Set (Σ k, G k)} {S : ∀ k, List (G k)} (hS : SymsIn R S)
    (j : K) (b : G j) (hb : (⟨j, b⟩ : Σ k, G k) ∈ R) :
    SymsIn R (Function.update S j (b :: S j)) := by
  intro k a ha
  by_cases hk : k = j
  · subst hk
    simp only [Function.update_self, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hb
    · exact hS k a ha
  · rw [Function.update_of_ne hk] at ha
    exact hS k a ha

theorem symsIn_update_tail {R : Set (Σ k, G k)} {S : ∀ k, List (G k)} (hS : SymsIn R S)
    (j : K) : SymsIn R (Function.update S j (S j).tail) := by
  intro k a ha
  by_cases hk : k = j
  · subst hk
    simp only [Function.update_self] at ha
    exact hS k a (List.mem_of_mem_tail ha)
  · rw [Function.update_of_ne hk] at ha
    exact hS k a ha

theorem stepAux_symsIn (R : Set (Σ k, G k)) (q : Stmt G L V) (hq : pushed q ⊆ R)
    (v : V) (S : ∀ k, List (G k)) (hS : SymsIn R S) : SymsIn R (stepAux q v S).stk := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [pushed, Set.union_subset_iff] at hq
      exact ih hq.2 _ _ (symsIn_update_cons hS k (f v) (hq.1 ⟨v, rfl⟩))
  | peek k f q ih => exact ih hq _ _ hS
  | pop k f q ih => exact ih hq _ _ (symsIn_update_tail hS k)
  | load f q ih => exact ih hq _ _ hS
  | branch f p q ihp ihq =>
      simp only [pushed, Set.union_subset_iff] at hq
      simp only [stepAux]
      cases f v
      · exact ihq hq.2 v S hS
      · exact ihp hq.1 v S hS
  | goto f => exact hS
  | halt => exact hS

/-- Invariance along runs. -/
theorem iterate_symsIn (M : L → Stmt G L V) (R : Set (Σ k, G k))
    (hM : ∀ l, pushed (M l) ⊆ R) (n : ℕ) (c d : Cfg G L V) (hc : SymsIn R c.stk)
    (h : (run M)^[n] (some c) = some d) : SymsIn R d.stk := by
  induction n generalizing d with
  | zero => cases h; exact hc
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
              exact stepAux_symsIn R (M l) (hM l) v S (ih _ he)

/-! ### Transient peaks inside one statement -/

variable [Fintype K]

/-- The largest total stack length met while executing the primitive operations of one
statement, boundary configurations included. -/
def peakAux : Stmt G L V → V → (∀ k, List (G k)) → ℕ
  | .push k f q, v, S =>
      max (ShiTMStackGrowth.size S) (peakAux q v (Function.update S k (f v :: S k)))
  | .peek k f q, v, S => peakAux q (f v (S k).head?) S
  | .pop k f q, v, S =>
      max (ShiTMStackGrowth.size S) (peakAux q (f v (S k).head?) (Function.update S k (S k).tail))
  | .load f q, v, S => peakAux q (f v) S
  | .branch f p q, v, S => cond (f v) (peakAux p v S) (peakAux q v S)
  | .goto _, _, S => ShiTMStackGrowth.size S
  | .halt, _, S => ShiTMStackGrowth.size S

theorem size_le_peakAux (q : Stmt G L V) (v : V) (S : ∀ k, List (G k)) :
    ShiTMStackGrowth.size S ≤ peakAux q v S := by
  induction q generalizing v S with
  | push k f q ih => exact le_max_left _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact le_max_left _ _
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq =>
      simp only [peakAux]
      cases f v
      · exact ihq v S
      · exact ihp v S
  | goto f => exact le_rfl
  | halt => exact le_rfl

theorem stepAux_size_le_peakAux (q : Stmt G L V) (v : V) (S : ∀ k, List (G k)) :
    ShiTMStackGrowth.size (stepAux q v S).stk ≤ peakAux q v S := by
  induction q generalizing v S with
  | push k f q ih => exact le_trans (ih _ _) (le_max_right _ _)
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact le_trans (ih _ _) (le_max_right _ _)
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq =>
      simp only [peakAux, stepAux]
      cases f v
      · exact ihq v S
      · exact ihp v S
  | goto f => exact le_rfl
  | halt => exact le_rfl

/-- The transient peak of a statement exceeds its entry space by at most its push budget. -/
theorem peakAux_le (q : Stmt G L V) (v : V) (S : ∀ k, List (G k)) :
    peakAux q v S ≤ ShiTMStackGrowth.size S + ShiTMStackGrowth.pushBudget q := by
  induction q generalizing v S with
  | push k f q ih =>
      have h1 := ih v (Function.update S k (f v :: S k))
      have h2 := ShiTMStackGrowth.size_push_le S k (f v)
      simp only [peakAux, ShiTMStackGrowth.pushBudget]
      exact max_le (by omega) (by omega)
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
      have h1 := ih (f v (S k).head?) (Function.update S k (S k).tail)
      have h2 := ShiTMStackGrowth.size_pop_le S k
      simp only [peakAux, ShiTMStackGrowth.pushBudget]
      exact max_le (by omega) (by omega)
  | load f q ih => exact ih _ _
  | branch f p q ihp ihq =>
      simp only [peakAux, ShiTMStackGrowth.pushBudget]
      cases f v
      · exact le_trans (ihq v S) (Nat.add_le_add_left (le_max_right _ _) _)
      · exact le_trans (ihp v S) (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp [peakAux]
  | halt => simp [peakAux]

/-- Uniformly over a finite-label program, transient peaks exceed boundary space by at most
a machine-dependent constant. -/
theorem exists_transient_bound [Fintype L] (M : L → Stmt G L V) :
    ∃ C : ℕ, ∀ l v S, peakAux (M l) v S ≤ ShiTMStackGrowth.size S + C := by
  refine ⟨∑ l, ShiTMStackGrowth.pushBudget (M l), fun l v S => ?_⟩
  apply le_trans (peakAux_le (M l) v S)
  apply Nat.add_le_add_left
  exact Finset.single_le_sum (f := fun l => ShiTMStackGrowth.pushBudget (M l))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

end Generic

/-! ### Bundled machines -/

section Bundled

local notation "run" => ShiTMSubroutine.run

/-- Input symbols on the input stack together with every pushable symbol. -/
def reachSyms (tm : FinTM2) : Set (Σ k, tm.Γ k) :=
  Set.range (fun a : tm.Γ tm.k₀ => (⟨tm.k₀, a⟩ : Σ k, tm.Γ k)) ∪ ⋃ l, pushed (tm.m l)

theorem reachSyms_finite (tm : FinTM2) : (reachSyms tm).Finite := by
  have := tm.Γk₀Fin
  exact (Set.finite_range _).union (Set.finite_iUnion fun l => pushed_finite (tm.m l))

/-- The finite alphabet that stack `j` can ever hold. -/
def stackSyms (tm : FinTM2) (j : tm.K) : Set (tm.Γ j) :=
  {a | (⟨j, a⟩ : Σ k, tm.Γ k) ∈ reachSyms tm}

theorem stackSyms_finite (tm : FinTM2) (j : tm.K) : (stackSyms tm j).Finite :=
  (reachSyms_finite tm).preimage (fun _ _ _ _ h => sigma_mk_injective h)

theorem symsIn_initList (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    SymsIn (reachSyms tm) (initList tm xs).stk := by
  intro k a ha
  by_cases hk : k = tm.k₀
  · subst hk
    exact Or.inl ⟨a, rfl⟩
  · rw [initList_stk_ne tm xs k hk] at ha
    cases ha

/-- **Reachable alphabets.** Every symbol on stack `j` of any configuration reachable from an
input configuration lies in the fixed finite set `stackSyms tm j`. -/
theorem mem_stackSyms_of_reachable (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (t : ℕ)
    (c : tm.Cfg) (h : (run tm.m)^[t] (some (initList tm xs)) = some c)
    (j : tm.K) (a : tm.Γ j) (ha : a ∈ c.stk j) : a ∈ stackSyms tm j :=
  iterate_symsIn tm.m (reachSyms tm) (fun l => Set.subset_union_of_subset_right
    (Set.subset_iUnion (fun l => pushed (tm.m l)) l) _) t _ c (symsIn_initList tm xs) h j a ha

end Bundled

end ShiSpace
