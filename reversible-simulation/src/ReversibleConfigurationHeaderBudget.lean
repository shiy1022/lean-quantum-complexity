import ReversibleMachineInitializationBudget
import ReversibleConstantSequenceBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem initializationHeaderSchedule_rank_bound (tm : Turing.FinTM2) (backward : Bool)
    (ar : Bool × Nat) (ha : ar ∈ initializationHeaderSchedule tm backward) :
    ar.2 < Fintype.card (Option tm.Λ) + Fintype.card tm.σ := by
  have h : ar ∈ initializationHeaderRanks tm := by
    cases backward <;> simpa [initializationHeaderSchedule] using ha
  rcases List.mem_append.mp h with h | h
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    have hj := j.isLt
    dsimp
    omega
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    have hj := j.isLt
    dsimp
    omega

theorem machineInitializationBudget_header_address (tm : Turing.FinTM2) (backward : Bool)
    (capacity initial : Polynomial Nat) (n : Nat) (ar : Bool × Nat)
    (ha : ar ∈ initializationHeaderSchedule tm backward) :
    n + 18 * ar.2 + 18 ≤ (machineInitializationBudget tm capacity initial).eval n := by
  have hr := initializationHeaderSchedule_rank_bound tm backward ar ha
  simp only [machineInitializationBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

set_option backward.isDefEq.respectTransparency false in
theorem configurationHeader_budget (tm : Turing.FinTM2) (backward : Bool)
    (capacity initial : Polynomial Nat) (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) ≤ capacity.eval n)
    (hbudget : CounterBudget cs (.inr 10) ((machineInitializationBudget tm capacity initial).eval n)) :
    CounterBudget ((packagedConfigurationHeader tm backward).counters n cs ys) (.inr 10)
      ((machineInitializationBudget tm capacity initial).eval n) := by
  apply constantSequence_counterBudget 0 0 0 backward (initializationHeaderSchedule tm backward) cs _ hbudget
  · exact (Nat.add_le_add_right hi 1).trans (machineInitializationBudget_capacity tm capacity initial n)
  · intro ar ha
    simpa only [hn, Nat.zero_mul, Nat.mul_zero, Nat.zero_add] using
      machineInitializationBudget_header_address tm backward capacity initial n ar ha

set_option backward.isDefEq.respectTransparency false in
theorem configurationHeader_layer_bound (tm : Turing.FinTM2) (backward : Bool)
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedConfigurationHeader tm backward).counters n cs ys (.inr 10) ≤
      cs (.inr 10) + (initializationHeaderSchedule tm backward).length * 630 := by
  exact constantSequence_layer_bound 0 0 0 backward (initializationHeaderSchedule tm backward) cs

set_option backward.isDefEq.respectTransparency false in
theorem configurationHeader_polynomial_bound (tm : Turing.FinTM2) (backward : Bool)
    (capacity initial layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n cs ys,
      cs (.inl 0) = n → cs (.inr 0) ≤ capacity.eval n →
      CounterBudget cs (.inr 10) ((machineInitializationBudget tm capacity initial).eval n) →
      cs (.inr 10) ≤ layers.eval n →
      (packagedConfigurationHeader tm backward).steps n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := constantSequence_budget_polynomial_bound 0 0 0 backward (initializationHeaderSchedule tm backward)
    (machineInitializationBudget tm capacity initial) layers
  refine ⟨clock, ?_⟩
  intro n cs ys hn hi hbudget hl
  apply hc n cs hbudget hl
  · exact (Nat.add_le_add_right hi 1).trans (machineInitializationBudget_capacity tm capacity initial n)
  · intro ar ha
    simpa only [hn, Nat.zero_mul, Nat.mul_zero, Nat.zero_add] using
      machineInitializationBudget_header_address tm backward capacity initial n ar ha

end ShiReversibleGenerator
