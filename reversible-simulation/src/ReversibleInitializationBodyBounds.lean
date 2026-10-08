import ReversibleInitializationInputBody

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding

noncomputable def initializationPreparedPolynomials (sizes : InitializationRegister → Polynomial Nat) := by
  classical
  exact operationResultPolynomial initializationAddressOperations
    (fun r => if r ∈ initializationAddressCleanup then 0 else sizes r)

theorem initializationPreparedPolynomials_eval (sizes : InitializationRegister → Polynomial Nat) (n : Nat) :
    (fun r => (initializationPreparedPolynomials sizes r).eval n) =
      initializationAddressResult (fun r => (sizes r).eval n) := by
  classical
  rw [initializationPreparedPolynomials, operationResultPolynomial_eval]
  congr 1
  funext r
  by_cases hr : r ∈ initializationAddressCleanup <;> simp [cleanupCounters_apply, hr]

noncomputable def initializationAddressClock (sizes : InitializationRegister → Polynomial Nat) := by
  classical
  exact cleanupClock initializationAddressCleanup sizes +
    operationClock initializationAddressOperations
      (fun r => if r ∈ initializationAddressCleanup then 0 else sizes r)

theorem initializationAddressClock_eval (sizes : InitializationRegister → Polynomial Nat) (n : Nat) :
    (initializationAddressClock sizes).eval n =
      cleanupSteps initializationAddressCleanup (fun r => (sizes r).eval n) +
        operationSteps initializationAddressOperations
          (cleanupCounters initializationAddressCleanup (fun r => (sizes r).eval n)) := by
  classical
  simp only [initializationAddressClock, Polynomial.eval_add, cleanupClock_eval, operationClock_eval]
  congr 1
  congr 1
  funext r
  by_cases hr : r ∈ initializationAddressCleanup <;> simp [cleanupCounters_apply, hr]

/-- Runtime cell and coordinate counters need only polynomial upper bounds. -/
theorem initializationInputBody_polynomial_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool)
    (sizes : InitializationRegister → Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat),
      (∀ r, cs r ≤ (sizes r).eval n) →
      initializationInputBodySteps tm e a backward cs ≤ clock.eval n := by
  let preparedSizes := initializationPreparedPolynomials sizes
  obtain ⟨clock, hc⟩ := conditionalPrinter_polynomial_bound initializationNodeRegisters
    (initializationInputYes tm e a backward) (initializationInputNo tm a backward)
    (Sum.inr 4 : InitializationRegister) (.inl 0) (.inr 5) (.inr 6) (by decide) preparedSizes
  refine ⟨initializationAddressClock sizes + clock, ?_⟩
  intro n cs h
  have hprep : ∀ r, initializationAddressResult cs r ≤ (preparedSizes r).eval n := by
    intro r
    change initializationAddressResult cs r ≤ (initializationPreparedPolynomials sizes r).eval n
    rw [congrFun (initializationPreparedPolynomials_eval sizes n) r]
    exact operationResult_mono initializationAddressOperations _ _
      (cleanupCounters_mono initializationAddressCleanup cs _ h) r
  have ha := Nat.add_le_add (cleanupSteps_mono initializationAddressCleanup cs _ h)
    (operationSteps_mono initializationAddressOperations _ _
      (cleanupCounters_mono initializationAddressCleanup cs _ h))
  rw [Polynomial.eval_add, initializationAddressClock_eval]
  exact Nat.add_le_add ha (hc n (initializationAddressResult cs) hprep)

theorem initializationInputBody_preserves_metadata (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat)
    (r : WorkspaceRegister) :
    initializationInputBodyCounters tm e a backward cs (.inl r) = cs (.inl r) := by
  rw [initializationInputBodyCounters, fixedNodeCounters_other]
  · simp [initializationAddress_result]
  all_goals simp [initializationNodeRegisters]

theorem initializationInputBody_preserves_index (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) :
    initializationInputBodyCounters tm e a backward cs (.inr 0) = cs (.inr 0) := by
  rw [initializationInputBodyCounters, fixedNodeCounters_other]
  · simp [initializationAddress_result]
  all_goals simp [initializationNodeRegisters]

theorem initializationInputBody_preserves_coordinate (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) :
    initializationInputBodyCounters tm e a backward cs (.inr 1) = cs (.inr 1) := by
  rw [initializationInputBodyCounters, fixedNodeCounters_other]
  · simp [initializationAddress_result]
  all_goals simp [initializationNodeRegisters]

end ShiReversibleGenerator
