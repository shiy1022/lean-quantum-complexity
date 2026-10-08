import ReversibleInitializationStart
import ReversibleAscendingSymbolBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def ascendingInitializationStartCounters (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :=
  Function.update (initializationPreludeCounters tm time n) (.inr 11)
    ((initializationCapacityPolynomial tm time).eval n)

theorem ascendingInitializationStart_counterBudget (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    CounterBudget (ascendingInitializationStartCounters tm time n) (.inr 10)
      ((initializationAddressBudget tm (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n) := by
  apply CounterBudget.update
  · intro r hr
    cases r with
    | inl r =>
        exact (resourceCounterBudgetPolynomial_bound tm time n r).trans
          (initializationAddressBudget_initial tm _ _ n)
    | inr r => exact Nat.zero_le _
  · exact initializationAddressBudget_capacity tm _ _ n

theorem ascendingInitializationStart_invariant (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (time : Polynomial Nat) (n : Nat)
    (pc : Option (SymbolSequenceLabels
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
      (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 4)))
    (ys : List Bool) :
    AscendingSymbolBudgetInvariant
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
      (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)
      ((initializationAddressBudget tm (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n)
      0 ((initializationCapacityPolynomial tm time).eval n) n ((initializationCapacityPolynomial tm time).eval n)
      ⟨pc, ascendingInitializationStartCounters tm time n, ys⟩ := by
  refine ⟨⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩, ascendingInitializationStart_counterBudget tm time n, ?_⟩
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, resourceResult_raw]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, resourceResult_capacity,
      initializationCapacityPolynomial]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, workspaceResult_buffer]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters, workspaceResult_scratch]
  · simp [ascendingInitializationStartCounters, initializationPreludeCounters]

/-- The runtime cell count is obtained by an actual nonconsuming affine copy of the prelude's capacity. -/
theorem ascendingInitializationStart_copy_run {L : Type} (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) (ys : List Bool) :
    CounterRun (affineCode caller 0 1 (.inl 2) (.inr 11) (.inl 5) stop)
      ⟨some (affineStart 0 1 stop), initializationPreludeCounters tm time n, ys⟩
      (7 * (initializationCapacityPolynomial tm time).eval n + 2)
      ⟨some (.inr (.inr stop)), ascendingInitializationStartCounters tm time n, ys⟩ := by
  have h := AffineAtom.run (⟨.inl 2, .inr 11, 0, 1⟩ : AffineAtom InitializationRegister) caller (.inl 5) stop
    (by simp [AffineAtom.Valid]) (initializationPreludeCounters tm time n)
    (by simp [initializationPreludeCounters, workspaceResult_scratch]) ys
  have hc : initializationPreludeCounters tm time n (.inl 2) = (initializationCapacityPolynomial tm time).eval n := by
    simp [initializationPreludeCounters, initializationCapacityPolynomial, resourceResult_capacity]
  have hz : initializationPreludeCounters tm time n (.inr 11) = 0 := rfl
  have he : (⟨.inl 2, .inr 11, 0, 1⟩ : AffineAtom InitializationRegister).apply
      (initializationPreludeCounters tm time n) = ascendingInitializationStartCounters tm time n := by
    simp only [AffineAtom.apply, ascendingInitializationStartCounters, hz, hc, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  rw [he] at h
  simpa only [AffineAtom.steps, hc, Nat.one_mul, Nat.add_zero] using h

end ShiReversibleGenerator
