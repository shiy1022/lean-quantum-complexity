import «AMPUNI-repeat-clocked-cleanup»
import «AMPUNI-clocked-cleanup-interface»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section

namespace ShiTMRepeatClocked
open ShiTMTypedTimeout
variable {K L sig : Type} [DecidableEq K] [Fintype K] {Gam : K → Type}
variable (output : K) (initial : sig)

/-- A bounded successful source run reaches the active handoff within linear overhead. -/
theorem preserves_bounded_run [Fintype L] (M : L → Stmt Gam L sig) :
    ∃ C : Nat, ∀ (budget steps : Nat) (c : Cfg Gam L sig) (v : sig)
      (S : ∀ k, List (Gam k)),
      (ShiTMSubroutine.run M)^[steps] (some c) = some ⟨none, v, S⟩ →
      steps ≤ budget →
      ∃ t : Nat,
        (run output initial M)^[t]
          (some (startCfg output (List.replicate budget true) c)) =
            some (activeFinish output initial (S output)) ∧
        t ≤ (C + 3) * budget + ShiTMStackGrowth.size c.stk +
          Fintype.card (ClockK K) + 2 := by
  obtain ⟨C, hg⟩ := ShiTMStackGrowth.finite_growth M
  refine ⟨C, ?_⟩
  intro budget steps c v S hr hb
  have hs := ShiTMStackGrowth.run_size_le M C hg steps c
    ⟨none, v, S⟩ hr
  change ShiTMStackGrowth.size S ≤
    ShiTMStackGrowth.size c.stk + steps * C at hs
  have hrep : List.replicate budget true =
      List.replicate steps true ++
        List.replicate (budget - steps) true := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hrun := preserves_exact_run output initial M steps c v S
    (List.replicate (budget - steps) true) hr
  rw [← hrep] at hrun
  have hc := ShiTMGenericCleanup.cleanup_cost_le
    (Sum.inl output : ClockK K)
    (liftStk (List.replicate (budget - steps) true) S)
  rw [ShiTMClockedCleanup.liftStk_size, List.length_replicate] at hc
  have hm := Nat.mul_le_mul_left C hb
  have hrest := Nat.sub_le budget steps
  exact ⟨_, hrun, by nlinarith⟩

end ShiTMRepeatClocked

namespace ShiTMRepeatClockedInterface
variable (tm : Turing.FinTM2)
local instance : Fintype tm.K := tm.kFin
local instance : Fintype tm.Λ := tm.ΛFin

theorem valid_with_budget :
    ∃ C : Nat, ∀ (budget : Nat)
      (xs : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁)),
      Nonempty (Turing.TM2OutputsInTime tm xs (some ys) budget) →
      ∃ t : Nat,
        (ShiTMRepeatClocked.run tm.k₁ tm.initialState tm.m)^[t]
          (some (ShiTMRepeatClocked.startCfg tm.k₁
            (List.replicate budget true) (Turing.initList tm xs))) =
          some (ShiTMRepeatClocked.activeFinish tm.k₁ tm.initialState ys) ∧
        t ≤ (C + 3) * budget + xs.length +
          Fintype.card (ShiTMTypedTimeout.ClockK tm.K) + 2 := by
  obtain ⟨C, h⟩ :=
    ShiTMRepeatClocked.preserves_bounded_run
      tm.k₁ tm.initialState tm.m
  refine ⟨C, ?_⟩
  intro budget xs ys valid
  obtain ⟨⟨⟨steps, hr⟩, hb⟩⟩ := valid
  let S := (Turing.haltList tm ys).stk
  have hr' : (ShiTMSubroutine.run tm.m)^[steps]
      (some (Turing.initList tm xs)) =
        some ⟨none, tm.initialState, S⟩ := hr
  have ho : S tm.k₁ = ys := by simp [S, Turing.haltList]
  obtain ⟨t, hrun, ht⟩ := h budget steps
    (Turing.initList tm xs) tm.initialState S hr' hb
  refine ⟨t, ?_, ?_⟩
  · simpa only [ho] using hrun
  · simpa only [ShiTMClockedInterface.initial_size] using ht

theorem valid_with_quadratic_budget (k : Nat) :
    ∃ D : Nat, ∀ (xs : List (tm.Γ tm.k₀))
      (ys : List (tm.Γ tm.k₁)),
      Nonempty (Turing.TM2OutputsInTime tm xs (some ys)
        (k * (xs.length + 1) ^ 2)) →
      ∃ t : Nat,
        (ShiTMRepeatClocked.run tm.k₁ tm.initialState tm.m)^[t]
          (some (ShiTMRepeatClocked.startCfg tm.k₁
            (List.replicate (k * (xs.length + 1) ^ 2) true)
            (Turing.initList tm xs))) =
          some (ShiTMRepeatClocked.activeFinish tm.k₁ tm.initialState ys) ∧
        t ≤ D * (xs.length + 1) ^ 2 := by
  obtain ⟨C, h⟩ := valid_with_budget tm
  let a := Fintype.card (ShiTMTypedTimeout.ClockK tm.K)
  refine ⟨(C + 3) * k + a + 3, ?_⟩
  intro xs ys hv
  obtain ⟨t, hr, ht⟩ := h (k * (xs.length + 1) ^ 2) xs ys hv
  have hx : xs.length ≤ (xs.length + 1) ^ 2 := by nlinarith
  have hq : 1 ≤ (xs.length + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left (a + 2) hq
  refine ⟨t, hr, ?_⟩
  change t ≤ (C + 3) * (k * (xs.length + 1) ^ 2) +
    xs.length + a + 2 at ht
  nlinarith

end ShiTMRepeatClockedInterface
