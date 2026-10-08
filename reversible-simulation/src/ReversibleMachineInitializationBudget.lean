import ReversiblePreparedComponentResources
import ReversibleRankedInitializerProgram
import ReversibleInitializationAddressBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- One fixed polynomial budget covers all stack ranks and ranked symbol addresses. -/
noncomputable def machineInitializationBudget (tm : Turing.FinTM2) (capacity initial : Polynomial Nat) : Polynomial Nat :=
  initial + capacity + Polynomial.X + Polynomial.C 18 *
    (Polynomial.C (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) +
      (Polynomial.C (Fintype.card tm.K) * capacity + capacity) *
        Polynomial.C (Fintype.card (Option (MachineSymbol tm))) +
      Polynomial.C (Fintype.card (Option (MachineSymbol tm)))) + Polynomial.C 18

theorem machineInitializationBudget_initial (tm : Turing.FinTM2) (capacity initial : Polynomial Nat) (n : Nat) :
    initial.eval n ≤ (machineInitializationBudget tm capacity initial).eval n := by
  simp only [machineInitializationBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

theorem machineInitializationBudget_capacity (tm : Turing.FinTM2) (capacity initial : Polynomial Nat) (n : Nat) :
    capacity.eval n + 1 ≤ (machineInitializationBudget tm capacity initial).eval n := by
  simp only [machineInitializationBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

theorem machineInitializationBudget_address (tm : Turing.FinTM2) (capacity initial : Polynomial Nat)
    (n : Nat) (k : tm.K) (rank : Nat) (hrank : rank < Fintype.card (Option (MachineSymbol tm))) :
    n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
      (((Fintype.equivFin tm.K) k).val * capacity.eval n + capacity.eval n) *
        Fintype.card (Option (MachineSymbol tm)) + rank) + 18 ≤
      (machineInitializationBudget tm capacity initial).eval n := by
  have hk := (((Fintype.equivFin tm.K) k).isLt).le
  have hm := Nat.mul_le_mul_right (capacity.eval n) hk
  have hs := Nat.mul_le_mul_right (Fintype.card (Option (MachineSymbol tm)))
    (Nat.add_le_add_right hm (capacity.eval n))
  simp only [machineInitializationBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Every actual stack program meets the same resource contract at its fixed machine rank. -/
noncomputable def packagedInitializationStack_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity initial : Polynomial Nat) (k : tm.K) :
    InitializationResources (packagedInitializationStack tm e backward k) capacity
      (machineInitializationBudget tm capacity initial) := by
  classical
  have hinput : ∀ n ar, ar ∈ initializationSymbolSchedule tm backward →
      n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
        (((Fintype.equivFin tm.K) k).val * capacity.eval n + capacity.eval n) *
          Fintype.card (Option (MachineSymbol tm)) + ar.2) + 18 ≤
        (machineInitializationBudget tm capacity initial).eval n := by
    intro n ar ha
    exact machineInitializationBudget_address tm capacity initial n k ar.2
      (initializationSymbolSchedule_rank_bound tm backward ar ha)
  have hconstant : ∀ n ar, ar ∈ initializationConstantSchedule tm backward →
      n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
        (((Fintype.equivFin tm.K) k).val * capacity.eval n + capacity.eval n) *
          Fintype.card (Option (MachineSymbol tm)) + ar.2) + 18 ≤
        (machineInitializationBudget tm capacity initial).eval n := by
    intro n ar ha
    exact machineInitializationBudget_address tm capacity initial n k ar.2
      (initializationConstantSchedule_rank_bound tm backward ar ha)
  unfold packagedInitializationStack
  dsimp only
  split_ifs with hk hb hb
  · exact packagedAscendingInputComponent_resources _ _ _ tm e backward _ capacity _ hinput
  · exact packagedInputComponent_resources _ _ _ tm e backward _ capacity _ hinput
  · exact packagedAscendingConstantComponent_resources _ _ _ backward _ capacity _ hconstant
  · exact packagedConstantComponent_resources _ _ _ backward _ capacity _ hconstant

/-- The full fixed list of stacks has an actual polynomial instruction clock under the shared budget. -/
theorem rankedInitializerStacks_polynomial_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity initial layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n cs ys,
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) ((machineInitializationBudget tm capacity initial).eval n) →
      cs (.inr 10) ≤ layers.eval n →
      initializerSequenceSteps ((initializationStackSchedule tm backward).map (packagedInitializationStack tm e backward))
        n cs ys ≤ clock.eval n := by
  apply initializerSequence_polynomial_bound _ capacity (machineInitializationBudget tm capacity initial) _ layers
  intro c hc
  classical
  let h := List.mem_map.mp hc
  let k := Classical.choose h
  have he : packagedInitializationStack tm e backward k = c := (Classical.choose_spec h).2
  exact he ▸ packagedInitializationStack_resources tm e backward capacity initial k

end ShiReversibleGenerator
