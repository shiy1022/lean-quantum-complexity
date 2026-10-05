/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Run algebra and all-prefix bounds (plan task S02).
-/
import Space.Model

set_option autoImplicit false

/-!
# Iterated runs of a TM2 program

`ShiTMSubroutine.run M` steps an optional configuration; `none` is absorbing. A configuration
with label `none` is *halted*: it is still reachable (and counted by `SpaceBoundedOn`), and the
next step returns `none`. This file makes those conventions explicit, so later proofs need not
unfold `Option.bind` or guess whether halting costs an extra step.
-/

namespace ShiSpace

open Turing Turing.TM2

section Generic

variable {K L V : Type} [DecidableEq K] {G : K → Type}

/-- Shorthand for the baseline single-step function on optional configurations. -/
local notation "run" => ShiTMSubroutine.run

theorem run_none (M : L → Stmt G L V) : run M none = none := rfl

theorem run_some (M : L → Stmt G L V) (c : Cfg G L V) : run M (some c) = step M c := rfl

theorem iterate_run_none (M : L → Stmt G L V) (n : ℕ) : (run M)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem iterate_run_add (M : L → Stmt G L V) (a b : ℕ) (c : Option (Cfg G L V)) :
    (run M)^[a + b] c = (run M)^[a] ((run M)^[b] c) :=
  Function.iterate_add_apply _ a b c

theorem iterate_run_succ (M : L → Stmt G L V) (n : ℕ) (c : Cfg G L V) :
    (run M)^[n + 1] (some c) = (run M)^[n] (step M c) :=
  Function.iterate_succ_apply _ n _

theorem iterate_run_succ' (M : L → Stmt G L V) (n : ℕ) (c : Option (Cfg G L V)) :
    (run M)^[n + 1] c = run M ((run M)^[n] c) :=
  Function.iterate_succ_apply' _ n c

/-- A configuration is halted exactly when it carries no label. -/
def Halted (c : Cfg G L V) : Prop := c.l = none

theorem step_halted (M : L → Stmt G L V) (c : Cfg G L V) (h : Halted c) :
    step M c = none := by
  rcases c with ⟨l, v, S⟩
  cases h
  rfl

theorem step_label (M : L → Stmt G L V) (l : L) (v : V) (S : ∀ k, List (G k)) :
    step M ⟨some l, v, S⟩ = some (stepAux (M l) v S) := rfl

theorem step_eq_none_iff (M : L → Stmt G L V) (c : Cfg G L V) :
    step M c = none ↔ Halted c := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => simp [Halted, step]
  | some l => simp [Halted, step]

/-- Once a run reaches a halted configuration, every later iterate is `none`. -/
theorem iterate_after_halt (M : L → Stmt G L V) (c d : Cfg G L V) (s t : ℕ)
    (hs : (run M)^[s] (some c) = some d) (hd : Halted d) (hst : s < t) :
    (run M)^[t] (some c) = none := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 + s := ⟨t - s - 1, by omega⟩
  rw [iterate_run_add, hs, iterate_run_succ, step_halted M d hd, iterate_run_none]

/-- Prefixes of a successful run are configurations. -/
theorem iterate_prefix (M : L → Stmt G L V) (c d : Cfg G L V) (s t : ℕ)
    (hs : (run M)^[s] (some c) = some d) (hts : t ≤ s) :
    ∃ e, (run M)^[t] (some c) = some e := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + t := ⟨s - t, by omega⟩
  rw [iterate_run_add] at hs
  cases h : (run M)^[t] (some c) with
  | none => rw [h, iterate_run_none] at hs; cases hs
  | some e => exact ⟨e, rfl⟩

/-- A halted configuration reached by a run is reached at a unique time. -/
theorem halted_time_unique (M : L → Stmt G L V) (c d e : Cfg G L V) (s t : ℕ)
    (hs : (run M)^[s] (some c) = some d) (hd : Halted d)
    (ht : (run M)^[t] (some c) = some e) : t ≤ s := by
  by_contra h
  rw [iterate_after_halt M c d s t hs hd (by omega)] at ht
  cases ht

/-- Uniqueness of the halted configuration. -/
theorem halted_unique (M : L → Stmt G L V) (c d e : Cfg G L V) (s t : ℕ)
    (hs : (run M)^[s] (some c) = some d) (hd : Halted d)
    (ht : (run M)^[t] (some c) = some e) (he : Halted e) : d = e := by
  have h1 := halted_time_unique M c d e s t hs hd ht
  have h2 := halted_time_unique M c e d t s ht he hs
  have : s = t := le_antisymm h2 h1
  subst this
  rw [hs] at ht
  exact Option.some.inj ht

/-- **All-prefix principle.** To bound every configuration reachable from `c`, it suffices to
bound those at times up to a halting time `s`; later iterates are `none`. -/
theorem forall_reachable_of_halts (M : L → Stmt G L V) (P : Cfg G L V → Prop)
    (c d : Cfg G L V) (s : ℕ) (hs : (run M)^[s] (some c) = some d) (hd : Halted d)
    (hP : ∀ t ≤ s, ∀ e, (run M)^[t] (some c) = some e → P e) :
    ∀ t e, (run M)^[t] (some c) = some e → P e := by
  intro t e ht
  by_cases hts : t ≤ s
  · exact hP t hts e ht
  · rw [iterate_after_halt M c d s t hs hd (by omega)] at ht
    cases ht

/-- Shifting the base point of a run. -/
theorem iterate_shift (M : L → Stmt G L V) (c d : Cfg G L V) (s t : ℕ)
    (hs : (run M)^[s] (some c) = some d) :
    (run M)^[t + s] (some c) = (run M)^[t] (some d) := by
  rw [iterate_run_add, hs]

end Generic

/-! ### Bundled machines -/

section Bundled

local notation "run" => ShiTMSubroutine.run

/-- The data of a successful `TM2Outputs` run in iterator form. -/
theorem iterate_of_outputs {tm : FinTM2} {xs : List (tm.Γ tm.k₀)} {ys : List (tm.Γ tm.k₁)}
    (h : TM2Outputs tm xs (some ys)) :
    (run tm.m)^[h.steps] (some (initList tm xs)) = some (haltList tm ys) :=
  h.evals_in_steps

theorem halted_haltList (tm : FinTM2) (ys : List (tm.Γ tm.k₁)) :
    Halted (haltList tm ys) := rfl

/-- `SpaceBoundedOn` for a terminating machine reduces to the configurations up to the
halting time. -/
theorem spaceBoundedOn_of_outputs {tm : FinTM2} {xs : List (tm.Γ tm.k₀)}
    {ys : List (tm.Γ tm.k₁)} (h : TM2Outputs tm xs (some ys)) (s : ℕ)
    (hb : ∀ t ≤ h.steps, ∀ e,
      (run tm.m)^[t] (some (initList tm xs)) = some e → cfgSpace tm e ≤ s) :
    SpaceBoundedOn tm xs s :=
  forall_reachable_of_halts tm.m (fun e => cfgSpace tm e ≤ s) _ _ h.steps (iterate_of_outputs h)
    (halted_haltList tm ys) hb

/-- In a terminating run, every reachable configuration occurs no later than the halt. -/
theorem le_steps_of_outputs {tm : FinTM2} {xs : List (tm.Γ tm.k₀)} {ys : List (tm.Γ tm.k₁)}
    (h : TM2Outputs tm xs (some ys)) (t : ℕ) (e : tm.Cfg)
    (ht : (run tm.m)^[t] (some (initList tm xs)) = some e) : t ≤ h.steps :=
  halted_time_unique tm.m _ _ _ _ _ (iterate_of_outputs h) (halted_haltList tm ys) ht

end Bundled

end ShiSpace
