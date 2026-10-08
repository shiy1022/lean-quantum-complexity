import ReversibleConstantStackClock
import ReversibleAscendingInitializationStart

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem constantInitializationStart_counterBudget (tm : Turing.FinTM2) (stackRank : Nat) (time : Polynomial Nat) (n : Nat) :
    CounterBudget (initializationStartCounters tm time n) (.inr 10)
      ((initializationConstantAddressBudget tm stackRank (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n) := by
  apply CounterBudget.update
  · intro r hr
    cases r with
    | inl r =>
        exact (resourceCounterBudgetPolynomial_bound tm time n r).trans
          (initializationConstantAddressBudget_initial tm stackRank _ _ n)
    | inr r => exact Nat.zero_le _
  · exact initializationConstantAddressBudget_capacity tm stackRank _ _ n

theorem constantInitializationStart_invariant (tm : Turing.FinTM2) (stackRank : Nat)
    (backward : Bool) (time : Polynomial Nat) (n : Nat)
    (pc : Option (ConstantSequenceLabels
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
      (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3)))
    (ys : List Bool) :
    ConstantCellBudgetInvariant
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
      (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)
      ((initializationConstantAddressBudget tm stackRank (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n)
      0 ((initializationCapacityPolynomial tm time).eval n) n ((initializationCapacityPolynomial tm time).eval n)
      ⟨pc, initializationStartCounters tm time n, ys⟩ := by
  refine ⟨⟨le_rfl, ?_, ?_, ?_, ?_⟩, constantInitializationStart_counterBudget tm stackRank time n, ?_⟩
  · simp [initializationStartCounters, initializationPreludeCounters, resourceResult_raw]
  · simp [initializationStartCounters, initializationPreludeCounters, resourceResult_capacity,
      initializationCapacityPolynomial]
  · simp [initializationStartCounters, initializationPreludeCounters, workspaceResult_buffer]
  · simp [initializationStartCounters, initializationPreludeCounters, workspaceResult_scratch]
  · simp [initializationStartCounters, initializationPreludeCounters]

theorem ascendingConstantInitializationStart_counterBudget (tm : Turing.FinTM2) (stackRank : Nat) (time : Polynomial Nat) (n : Nat) :
    CounterBudget (ascendingInitializationStartCounters tm time n) (.inr 10)
      ((initializationConstantAddressBudget tm stackRank (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n) := by
  apply CounterBudget.update
  · intro r hr
    cases r with
    | inl r =>
        exact (resourceCounterBudgetPolynomial_bound tm time n r).trans
          (initializationConstantAddressBudget_initial tm stackRank _ _ n)
    | inr r => exact Nat.zero_le _
  · exact initializationConstantAddressBudget_capacity tm stackRank _ _ n

theorem ascendingConstantInitializationStart_invariant (tm : Turing.FinTM2) (stackRank : Nat)
    (backward : Bool) (time : Polynomial Nat) (n : Nat)
    (pc : Option (ConstantSequenceLabels
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
      (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 4)))
    (ys : List Bool) :
    AscendingConstantBudgetInvariant
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
      (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)
      ((initializationConstantAddressBudget tm stackRank (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n)
      0 ((initializationCapacityPolynomial tm time).eval n) n ((initializationCapacityPolynomial tm time).eval n)
      ⟨pc, ascendingInitializationStartCounters tm time n, ys⟩ := by
  refine ⟨⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩, ascendingConstantInitializationStart_counterBudget tm stackRank time n, ?_⟩
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, resourceResult_raw]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, resourceResult_capacity,
      initializationCapacityPolynomial]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, workspaceResult_buffer]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, workspaceResult_scratch]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters]


end ShiReversibleGenerator
