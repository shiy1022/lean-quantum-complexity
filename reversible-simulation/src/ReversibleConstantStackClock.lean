import ReversibleConstantStackSchema
import ReversibleConstantTraversalBudget
import ReversibleAscendingConstantBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def initializationConstantAddressBudget (tm : Turing.FinTM2) (stackRank : Nat) (capacity initial : Polynomial Nat) : Polynomial Nat :=
  initial + capacity + Polynomial.X + Polynomial.C 18 *
    (Polynomial.C (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) +
      Polynomial.C (stackRank + 1) * capacity *
        Polynomial.C (Fintype.card (Option (MachineSymbol tm))) +
      Polynomial.C (Fintype.card (Option (MachineSymbol tm)))) + Polynomial.C 18

theorem initializationConstantAddressBudget_initial (tm : Turing.FinTM2) (stackRank : Nat) (capacity initial : Polynomial Nat) (n : Nat) :
    initial.eval n ≤ (initializationConstantAddressBudget tm stackRank capacity initial).eval n := by
  simp only [initializationConstantAddressBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

theorem initializationConstantAddressBudget_capacity (tm : Turing.FinTM2) (stackRank : Nat) (capacity initial : Polynomial Nat) (n : Nat) :
    capacity.eval n ≤ (initializationConstantAddressBudget tm stackRank capacity initial).eval n := by
  simp only [initializationConstantAddressBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/-- The machine ranks give a fixed polynomial budget covering every visited cell address. -/
theorem initializationConstantAddressBudget_addresses (tm : Turing.FinTM2) (stackRank : Nat) (capacity initial : Polynomial Nat)
    (backward : Bool) (n : Nat) (ar : Bool × Nat)
    (h : ar ∈ initializationConstantSchedule tm backward) :
    n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
      (stackRank * capacity.eval n + capacity.eval n) *
        Fintype.card (Option (MachineSymbol tm)) + ar.2) + 18 ≤
      (initializationConstantAddressBudget tm stackRank capacity initial).eval n := by
  have hr := initializationConstantSchedule_rank_bound tm backward ar h
  have he : stackRank * capacity.eval n + capacity.eval n =
      (stackRank + 1) * capacity.eval n := by ring
  rw [he]
  simp only [initializationConstantAddressBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/-- Specialization of the actual counted loop clock to the machine's fixed symbol schedule. -/
theorem initializationConstantStack_polynomial_bound (tm : Turing.FinTM2) (stackRank : Nat)
    (backward : Bool) (capacity initial layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg InitializationRegister (ConstantSequenceLabels
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
        (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3))),
      ConstantCellBudgetInvariant
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
        (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)
        ((initializationConstantAddressBudget tm stackRank capacity initial).eval n) (layers.eval n) (capacity.eval n) n count s →
      descendingSteps (constantCellBody
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
        (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (capacity.eval n) n)
        (constantCellCost (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
          (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)) count s ≤ clock.eval n := by
  exact constantCellTraversal_polynomial_bound _ _ _ backward (initializationConstantSchedule tm backward)
    capacity (initializationConstantAddressBudget tm stackRank capacity initial) layers
    (fun n ar h => initializationConstantAddressBudget_addresses tm stackRank capacity initial backward n ar h)

/-- Specialization of the actual counted loop clock to the machine's fixed symbol schedule. -/
theorem ascendingInitializationConstantStack_polynomial_bound (tm : Turing.FinTM2) (stackRank : Nat)
    (backward : Bool) (capacity initial layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg InitializationRegister (ConstantSequenceLabels
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
        (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 4))),
      AscendingConstantBudgetInvariant
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
        (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)
        ((initializationConstantAddressBudget tm stackRank capacity initial).eval n) (layers.eval n) (capacity.eval n) n count s →
      descendingSteps (ascendingConstantCellBody
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
        (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (capacity.eval n) n)
        (ascendingConstantCellCost (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
          (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)) count s ≤ clock.eval n := by
  exact ascendingConstantTraversal_polynomial_bound _ _ _ backward (initializationConstantSchedule tm backward)
    capacity (initializationConstantAddressBudget tm stackRank capacity initial) layers
    (fun n ar h => initializationConstantAddressBudget_addresses tm stackRank capacity initial backward n ar h)


end ShiReversibleGenerator
