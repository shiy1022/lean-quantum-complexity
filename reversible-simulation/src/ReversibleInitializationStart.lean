import ReversibleResourceCounterBounds

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def initializationCapacityPolynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :=
  Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1

noncomputable def initializationPreludeCounters (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    InitializationRegister → Nat :=
  Sum.elim (operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n))) (fun _ => 0)

noncomputable def initializationStartCounters (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :=
  Function.update (initializationPreludeCounters tm time n) (.inr 0)
    ((initializationCapacityPolynomial tm time).eval n)

theorem initializationStart_counterBudget (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    CounterBudget (initializationStartCounters tm time n) (.inr 10)
      ((initializationAddressBudget tm (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n) := by
  apply CounterBudget.update
  · intro r hr
    cases r with
    | inl r =>
        exact (resourceCounterBudgetPolynomial_bound tm time n r).trans
          (initializationAddressBudget_initial tm _ _ n)
    | inr r => exact Nat.zero_le _
  · exact initializationAddressBudget_capacity tm _ _ n

theorem initializationStart_invariant (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (time : Polynomial Nat) (n : Nat)
    (pc : Option (SymbolSequenceLabels
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
      (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3)))
    (ys : List Bool) :
    SymbolCellBudgetInvariant
      (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
      (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)
      ((initializationAddressBudget tm (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time)).eval n)
      0 ((initializationCapacityPolynomial tm time).eval n) n ((initializationCapacityPolynomial tm time).eval n)
      ⟨pc, initializationStartCounters tm time n, ys⟩ := by
  refine ⟨⟨le_rfl, ?_, ?_, ?_, ?_⟩, initializationStart_counterBudget tm time n, ?_⟩
  · simp [initializationStartCounters, initializationPreludeCounters, resourceResult_raw]
  · simp [initializationStartCounters, initializationPreludeCounters, resourceResult_capacity,
      initializationCapacityPolynomial]
  · simp [initializationStartCounters, initializationPreludeCounters, workspaceResult_buffer]
  · simp [initializationStartCounters, initializationPreludeCounters, workspaceResult_scratch]
  · simp [initializationStartCounters, initializationPreludeCounters]

/-- The runtime cell count is obtained by an actual nonconsuming affine copy of the prelude's capacity. -/
theorem initializationStart_copy_run {L : Type} (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) (ys : List Bool) :
    CounterRun (affineCode caller 0 1 (.inl 2) (.inr 0) (.inl 5) stop)
      ⟨some (affineStart 0 1 stop), initializationPreludeCounters tm time n, ys⟩
      (7 * (initializationCapacityPolynomial tm time).eval n + 2)
      ⟨some (.inr (.inr stop)), initializationStartCounters tm time n, ys⟩ := by
  have h := AffineAtom.run (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister) caller (.inl 5) stop
    (by simp [AffineAtom.Valid]) (initializationPreludeCounters tm time n)
    (by simp [initializationPreludeCounters, workspaceResult_scratch]) ys
  have hc : initializationPreludeCounters tm time n (.inl 2) = (initializationCapacityPolynomial tm time).eval n := by
    simp [initializationPreludeCounters, initializationCapacityPolynomial, resourceResult_capacity]
  have hz : initializationPreludeCounters tm time n (.inr 0) = 0 := rfl
  have he : (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister).apply
      (initializationPreludeCounters tm time n) = initializationStartCounters tm time n := by
    simp only [AffineAtom.apply, initializationStartCounters, hz, hc, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  rw [he] at h
  simpa only [AffineAtom.steps, hc, Nat.one_mul, Nat.add_zero] using h

end ShiReversibleGenerator
