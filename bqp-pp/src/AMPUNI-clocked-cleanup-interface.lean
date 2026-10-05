import «AMPUNI-clocked-cleanup-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMClockedInterface
variable (tm : Turing.FinTM2)
local instance sourceStacksFinite : Fintype tm.K := tm.kFin
local instance sourceLabelsFinite : Fintype tm.Λ := tm.ΛFin

abbrev run := ShiTMClockedCleanup.run tm.k₁ tm.initialState tm.m
abbrev start (budget : Nat) (xs : List (tm.Γ tm.k₀)) :=
  ShiTMClockedCleanup.startCfg tm.k₁ (List.replicate budget true) (Turing.initList tm xs)
abbrev finish (ys : List (tm.Γ tm.k₁)) :=
  ShiTMClockedCleanup.haltCfg (L := tm.Λ) tm.k₁ tm.initialState ys

theorem initial_size (xs : List (tm.Γ tm.k₀)) :
    ShiTMStackGrowth.size (K := tm.K) (G := tm.Γ) (Turing.initList tm xs).stk = xs.length := by
  have h : ∀ k, ((Turing.initList tm xs).stk k).length =
      if k = tm.k₀ then xs.length else 0 := by
    intro k
    by_cases hk : k = tm.k₀
    · subst k; simp [Turing.initList]
    · simp [Turing.initList, hk]
  unfold ShiTMStackGrowth.size
  simp_rw [h]
  simp

/-- Supplied fuel bounds every input, whether or not the source computation
is valid. The result has only its output stack populated and resets all state. -/
theorem total_with_budget :
    ∃ C : Nat, ∀ (budget : Nat) (xs : List (tm.Γ tm.k₀)),
      ∃ (t : Nat) (ys : List (tm.Γ tm.k₁)),
        (run tm)^[t] (some (start tm budget xs)) = some (finish tm ys) ∧
        t ≤ (C+1)*(2*budget+1)+xs.length+budget+
          Fintype.card (ShiTMTypedTimeout.ClockK tm.K)+2 := by
  obtain ⟨C, h⟩ := ShiTMClockedCleanup.total_from_fuel_bounded tm.k₁ tm.initialState tm.m
  refine ⟨C, ?_⟩
  intro budget xs
  obtain ⟨t, ys, hr, ht⟩ := h (List.replicate budget true) (Turing.initList tm xs)
  refine ⟨t, ys, hr, ?_⟩
  simpa only [List.length_replicate, initial_size] using ht

/-- Any source output certified within the supplied budget is preserved by
the clock and cleanup, with a uniform linear overhead. -/
theorem valid_with_budget :
    ∃ C : Nat, ∀ (budget : Nat) (xs : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁)),
      Nonempty (Turing.TM2OutputsInTime tm xs (some ys) budget) →
      ∃ t : Nat, (run tm)^[t] (some (start tm budget xs)) = some (finish tm ys) ∧
        t ≤ (C+3)*budget+xs.length+Fintype.card (ShiTMTypedTimeout.ClockK tm.K)+2 := by
  obtain ⟨C, h⟩ := ShiTMClockedCleanup.preserves_bounded_run tm.k₁ tm.initialState tm.m
  refine ⟨C, ?_⟩
  intro budget xs ys valid
  obtain ⟨⟨⟨steps, hr⟩, hb⟩⟩ := valid
  let S := (Turing.haltList tm ys).stk
  have hr' : (ShiTMSubroutine.run tm.m)^[steps] (some (Turing.initList tm xs)) =
      some ⟨none, tm.initialState, S⟩ := hr
  have ho : S tm.k₁ = ys := by simp [S, Turing.haltList]
  obtain ⟨t, hrun, ht⟩ := h budget steps (Turing.initList tm xs) tm.initialState S hr' hb
  refine ⟨t, ?_, ?_⟩
  · simpa only [ho] using hrun
  · simpa only [initial_size] using ht

/-- Quadratic supplied fuel gives a quadratic all-input execution bound.
This theorem starts with fuel already present; it does not construct it. -/
theorem total_with_quadratic_budget (k : Nat) :
    ∃ D : Nat, ∀ xs : List (tm.Γ tm.k₀),
      ∃ (t : Nat) (ys : List (tm.Γ tm.k₁)),
        (run tm)^[t] (some (start tm (k*(xs.length+1)^2) xs)) =
          some (finish tm ys) ∧ t ≤ D*(xs.length+1)^2 := by
  obtain ⟨C, h⟩ := total_with_budget tm
  let a := Fintype.card (ShiTMTypedTimeout.ClockK tm.K)
  refine ⟨(2*C+3)*k+C+a+4, ?_⟩
  intro xs
  obtain ⟨t, ys, hr, ht⟩ := h (k*(xs.length+1)^2) xs
  have hx : xs.length ≤ (xs.length+1)^2 := by nlinarith
  have hq : 1 ≤ (xs.length+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left (C+a+3) hq
  refine ⟨t, ys, hr, ?_⟩
  change t ≤ (C+1)*(2*(k*(xs.length+1)^2)+1)+xs.length+
    k*(xs.length+1)^2+a+2 at ht
  nlinarith

theorem valid_with_quadratic_budget (k : Nat) :
    ∃ D : Nat, ∀ (xs : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁)),
      Nonempty (Turing.TM2OutputsInTime tm xs (some ys) (k*(xs.length+1)^2)) →
      ∃ t : Nat,
        (run tm)^[t] (some (start tm (k*(xs.length+1)^2) xs)) =
          some (finish tm ys) ∧ t ≤ D*(xs.length+1)^2 := by
  obtain ⟨C, h⟩ := valid_with_budget tm
  let a := Fintype.card (ShiTMTypedTimeout.ClockK tm.K)
  refine ⟨(C+3)*k+a+3, ?_⟩
  intro xs ys hv
  obtain ⟨t, hr, ht⟩ := h (k*(xs.length+1)^2) xs ys hv
  have hx : xs.length ≤ (xs.length+1)^2 := by nlinarith
  have hq : 1 ≤ (xs.length+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left (a+2) hq
  refine ⟨t, hr, ?_⟩
  change t ≤ (C+3)*(k*(xs.length+1)^2)+xs.length+a+2 at ht
  nlinarith

end ShiTMClockedInterface
