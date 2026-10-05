/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Bounded run segments and their sequential composition (plan task S02).
-/
import Space.Frame

set_option autoImplicit false

/-!
# Peak-space segments

`Seg M c n d B`: the program `M` runs from `c` to `d` in exactly `n` steps, and **every**
configuration of that segment, both endpoints included, has total stack length at most `B`.
Sequential composition takes the maximum of the two peaks; repeated segments with a common
bound compose to a segment with that bound, however many there are. A segment ending in a
halted configuration bounds every reachable configuration.
-/

namespace ShiSpace

open Turing Turing.TM2

variable {K L V : Type} [DecidableEq K] [Fintype K] {G : K → Type}

local notation "run" => ShiTMSubroutine.run

/-- A run segment of `n` steps from `c` to `d` whose every configuration uses at most `B`. -/
def Seg (M : L → Stmt G L V) (c : Cfg G L V) (n : ℕ) (d : Cfg G L V) (B : ℕ) : Prop :=
  (run M)^[n] (some c) = some d ∧
    ∀ t ≤ n, ∀ e, (run M)^[t] (some c) = some e → ShiTMStackGrowth.size e.stk ≤ B

namespace Seg

variable {M : L → Stmt G L V}

theorem refl {c : Cfg G L V} {B : ℕ} (h : ShiTMStackGrowth.size c.stk ≤ B) : Seg M c 0 c B :=
  ⟨rfl, fun t ht e he => by
    obtain rfl : t = 0 := by omega
    cases he; exact h⟩

theorem mono {c d : Cfg G L V} {n B B' : ℕ} (h : Seg M c n d B) (hB : B ≤ B') :
    Seg M c n d B' :=
  ⟨h.1, fun t ht e he => le_trans (h.2 t ht e he) hB⟩

theorem start_le {c d : Cfg G L V} {n B : ℕ} (h : Seg M c n d B) :
    ShiTMStackGrowth.size c.stk ≤ B := h.2 0 (Nat.zero_le _) c rfl

theorem end_le {c d : Cfg G L V} {n B : ℕ} (h : Seg M c n d B) :
    ShiTMStackGrowth.size d.stk ≤ B := h.2 n le_rfl d h.1

/-- Sequential composition: the peak is the maximum of the two peaks. -/
theorem trans {c d e : Cfg G L V} {n m B₁ B₂ : ℕ} (h₁ : Seg M c n d B₁) (h₂ : Seg M d m e B₂) :
    Seg M c (m + n) e (max B₁ B₂) := by
  refine ⟨by rw [iterate_run_add, h₁.1, h₂.1], ?_⟩
  intro t ht x hx
  by_cases htn : t ≤ n
  · exact le_trans (h₁.2 t htn x hx) (le_max_left _ _)
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + n := ⟨t - n, by omega⟩
    rw [iterate_run_add, h₁.1] at hx
    exact le_trans (h₂.2 u (by omega) x hx) (le_max_right _ _)

/-- Composition at a common bound. -/
theorem trans' {c d e : Cfg G L V} {n m B : ℕ} (h₁ : Seg M c n d B) (h₂ : Seg M d m e B) :
    Seg M c (m + n) e B := by
  simpa using trans h₁ h₂

/-- One step as a segment. -/
theorem single {c d : Cfg G L V} {B : ℕ} (h : step M c = some d)
    (hc : ShiTMStackGrowth.size c.stk ≤ B) (hd : ShiTMStackGrowth.size d.stk ≤ B) :
    Seg M c 1 d B := by
  refine ⟨h, fun t ht e he => ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
  · cases he; exact hc
  · rw [show (run M)^[1] (some c) = step M c from rfl, h] at he
    cases he; exact hd

/-- Any number of segments sharing a bound `B` compose to one segment with bound `B`. This is
the scratch-reuse principle: the peak is not multiplied by the number of iterations. -/
theorem iter (c : ℕ → Cfg G L V) (n : ℕ → ℕ) (B N : ℕ)
    (h : ∀ i < N, Seg M (c i) (n i) (c (i + 1)) B) (h0 : ShiTMStackGrowth.size (c 0).stk ≤ B) :
    Seg M (c 0) (∑ i ∈ Finset.range N, n i) (c N) B := by
  induction N with
  | zero => simpa using refl h0
  | succ N ih =>
      rw [Finset.sum_range_succ, add_comm]
      exact trans' (ih fun i hi => h i (by omega)) (h N (by omega))

/-- A segment ending in a halted configuration bounds every reachable configuration. -/
theorem forall_of_halted {c d : Cfg G L V} {n B : ℕ} (h : Seg M c n d B) (hd : Halted d) :
    ∀ t e, (run M)^[t] (some c) = some e → ShiTMStackGrowth.size e.stk ≤ B :=
  forall_reachable_of_halts M _ c d n h.1 hd h.2

/-- Restricting a segment's bound to the stacks it may write: if every stack outside `A` is
untouched, the segment bound is the active peak plus the entry frame space. -/
theorem of_frame (A : Finset K) (hM : ∀ j ∉ A, ∀ l, writes j (M l) = false)
    {c d : Cfg G L V} {n Bact : ℕ} (hr : (run M)^[n] (some c) = some d)
    (hact : ∀ t ≤ n, ∀ e, (run M)^[t] (some c) = some e → sizeOn A e.stk ≤ Bact) :
    Seg M c n d (Bact + sizeOn Aᶜ c.stk) := by
  refine ⟨hr, fun t ht e he => ?_⟩
  rw [size_iterate_of_frame M A hM t c e he]
  exact Nat.add_le_add_right (hact t ht e he) _

end Seg

/-! ### Transfer along subroutine embeddings -/

section Lift

variable {A B : Type}

omit [Fintype K] in
/-- A subroutine run that ends at its terminal label never visits that label earlier. -/
theorem not_terminal_before (small : A → Stmt G A V) (terminal : A)
    (hterm : small terminal = .halt) (c d e : Cfg G A V) (n s : ℕ)
    (hn : (run small)^[n] (some c) = some d) (hd : d.l = some terminal)
    (hs : (run small)^[s] (some c) = some e) (hsn : s < n) : e.l ≠ some terminal := by
  intro he
  rcases e with ⟨l, v, S⟩
  change l = some terminal at he
  subst he
  have h1 : (run small)^[s + 1] (some c) = some ⟨none, v, S⟩ := by
    rw [iterate_run_succ', hs]
    simp [ShiTMSubroutine.run, step, hterm, stepAux]
  rcases Nat.lt_or_ge (s + 1) n with hlt | hge
  · rw [iterate_after_halt small c _ (s + 1) n h1 rfl hlt] at hn
    cases hn
  · obtain rfl : n = s + 1 := by omega
    rw [h1] at hn
    cases hn
    cases hd

omit [Fintype K] in
/-- Before reaching the terminal label, the embedded run is exactly the relabelled run. -/
theorem iterate_lift_before_terminal (small : A → Stmt G A V) (big : B → Stmt G B V)
    (f : A → B) (terminal : A)
    (hbody : ∀ l, l ≠ terminal → big (f l) = ShiTMSubroutine.stmt f (small l))
    (c : Option (Cfg G A V)) (t : ℕ)
    (hpre : ∀ s < t, ∀ e, (run small)^[s] c = some e → e.l ≠ some terminal) :
    (run big)^[t] (c.map (ShiTMSubroutine.cfg f)) =
      ((run small)^[t] c).map (ShiTMSubroutine.cfg f) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iterate_run_succ', iterate_run_succ', ih fun s hs => hpre s (by omega)]
      cases he : (run small)^[t] c with
      | none => rfl
      | some e =>
          have hne := hpre t (by omega) e he
          rcases e with ⟨l, v, S⟩
          cases l with
          | none => rfl
          | some l =>
              have hl : l ≠ terminal := fun h => hne (by rw [h])
              simp [ShiTMSubroutine.run, ShiTMSubroutine.cfg, step, hbody l hl,
                ShiTMSubroutine.stepAux_lift]

/-- A subroutine segment ending at its terminal label transfers to the host machine with the
same peak bound (relabelling does not change stacks). -/
theorem Seg.lift_terminal (small : A → Stmt G A V) (big : B → Stmt G B V)
    (f : A → B) (terminal : A) (hterm : small terminal = .halt)
    (hbody : ∀ l, l ≠ terminal → big (f l) = ShiTMSubroutine.stmt f (small l))
    {c d : Cfg G A V} {n Bd : ℕ} (h : Seg small c n d Bd) (hd : d.l = some terminal) :
    Seg big (ShiTMSubroutine.cfg f c) n (ShiTMSubroutine.cfg f d) Bd := by
  refine ⟨?_, ?_⟩
  · simpa using ShiTMSubroutine.run_to_terminal small big f terminal hterm hbody n (some c) d
      hd h.1
  · intro t ht e he
    have hpre : ∀ s < t, ∀ e, (run small)^[s] (some c) = some e → e.l ≠ some terminal :=
      fun s hs e' he' => not_terminal_before small terminal hterm c d e' n s h.1 hd he'
        (by omega)
    have hl := iterate_lift_before_terminal small big f terminal hbody (some c) t hpre
    simp only [Option.map_some] at hl
    rw [hl] at he
    cases hs : (run small)^[t] (some c) with
    | none => rw [hs] at he; cases he
    | some e' =>
        rw [hs] at he
        cases he
        exact h.2 t ht e' hs

end Lift

end ShiSpace
