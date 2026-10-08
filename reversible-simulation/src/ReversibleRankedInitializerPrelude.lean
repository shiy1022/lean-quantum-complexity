import ReversibleRankedInitializerForest
import ReversibleRankedInitializerClock

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem initializationPrelude_machineBudget (tm : Turing.FinTM2) (time : Polynomial Nat)
    (n : Nat) :
    CounterBudget (initializationPreludeCounters tm time n) (.inr 10)
      ((machineInitializationBudget tm (initializationCapacityPolynomial tm time)
        (resourceCounterBudgetPolynomial tm time)).eval n) := by
  intro r hr
  cases r with
  | inl r =>
    exact (resourceCounterBudgetPolynomial_bound tm time n r).trans
      (machineInitializationBudget_initial tm _ _ n)
  | inr r => exact Nat.zero_le _

/-- The actual prelude supplies every premise of the full initializer polynomial clock. -/
theorem rankedInitializer_prelude_clock (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n ys,
      initializerSequenceSteps (rankedInitializerComponents tm e backward) n
        (initializationPreludeCounters tm time n) ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := rankedInitializer_polynomial_bound tm e backward
    (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time) 0
  refine ⟨clock, ?_⟩
  intro n ys
  apply hc n (initializationPreludeCounters tm time n) ys
  · simp [initializationPreludeCounters, resourceResult_raw]
  · simp [initializationPreludeCounters, initializationCapacityPolynomial, resourceResult_capacity]
  · simp [initializationPreludeCounters, workspaceResult_buffer]
  · simp [initializationPreludeCounters, workspaceResult_scratch]
  · exact Nat.zero_le _
  · exact initializationPrelude_machineBudget tm time n
  · simp [initializationPreludeCounters]

/-- Actual counted execution from the prelude emits exactly the established initializer bytes. -/
theorem rankedInitializer_prelude_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (time : Polynomial Nat) (n : Nat) (ys : List Bool) :
    CounterRun (rankedInitializerCode tm e backward)
      ⟨some (initializerSequenceEntry (rankedInitializerComponents tm e backward)),
        initializationPreludeCounters tm time n, ys⟩
      (initializerSequenceSteps (rankedInitializerComponents tm e backward) n
        (initializationPreludeCounters tm time n) ys)
      ⟨some (initializerSequenceExit (rankedInitializerComponents tm e backward)),
        initializerSequenceCounters (rankedInitializerComponents tm e backward) n
          (initializationPreludeCounters tm time n) ys,
        ((if backward then (paddedForestCompile (fun i : Fin n => i.val) n 17
            (initialForest tm e ((initializationCapacityPolynomial tm time).eval n) n)).reverse
          else paddedForestCompile (fun i : Fin n => i.val) n 17
            (initialForest tm e ((initializationCapacityPolynomial tm time).eval n) n)).map
          (rawAssignmentPayload backward)).flatten ++ ys⟩ := by
  have hn : initializationPreludeCounters tm time n (.inl 0) = n := by
    simp [initializationPreludeCounters, resourceResult_raw]
  have hcap : initializationPreludeCounters tm time n (.inl 2) =
      (initializationCapacityPolynomial tm time).eval n := by
    simp [initializationPreludeCounters, initializationCapacityPolynomial, resourceResult_capacity]
  have h := rankedInitializer_run tm e backward n (initializationPreludeCounters tm time n) ys hn
    (by simp [initializationPreludeCounters, workspaceResult_buffer])
    (by simp [initializationPreludeCounters, workspaceResult_scratch])
  rw [rankedInitializer_output_forest tm e backward
    ((initializationCapacityPolynomial tm time).eval n) n
    (initializationPreludeCounters tm time n) ys hn hcap] at h
  exact h

end ShiReversibleGenerator
