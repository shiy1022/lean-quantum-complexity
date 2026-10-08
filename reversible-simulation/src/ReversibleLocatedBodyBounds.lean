import ReversibleLocatedInitializationBody

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard symbolRank : Nat)

noncomputable def cellCoordinatePolynomials (sizes : InitializationRegister → Polynomial Nat) :=
  operationResultPolynomial (cellCoordinateOperations header stackRank symbolCard symbolRank)
    (Function.update sizes (.inr 1) 0)

theorem cellCoordinatePolynomials_eval (sizes : InitializationRegister → Polynomial Nat) (n : Nat) :
    (fun r => (cellCoordinatePolynomials header stackRank symbolCard symbolRank sizes r).eval n) =
      cellCoordinateResult header stackRank symbolCard symbolRank (fun r => (sizes r).eval n) := by
  rw [cellCoordinatePolynomials, operationResultPolynomial_eval]
  congr 1
  funext r
  by_cases h : r = (Sum.inr 1 : InitializationRegister) <;> simp [cleanupCounters, h]

noncomputable def cellCoordinateClock (sizes : InitializationRegister → Polynomial Nat) :=
  cleanupClock [(Sum.inr 1 : InitializationRegister)] sizes +
    operationClock (cellCoordinateOperations header stackRank symbolCard symbolRank)
      (Function.update sizes (.inr 1) 0)

theorem cellCoordinateClock_eval (sizes : InitializationRegister → Polynomial Nat) (n : Nat) :
    (cellCoordinateClock header stackRank symbolCard symbolRank sizes).eval n =
      cleanupSteps [(Sum.inr 1 : InitializationRegister)] (fun r => (sizes r).eval n) +
        operationSteps (cellCoordinateOperations header stackRank symbolCard symbolRank)
          (cleanupCounters [.inr 1] (fun r => (sizes r).eval n)) := by
  simp only [cellCoordinateClock, Polynomial.eval_add, cleanupClock_eval, operationClock_eval]
  congr 1

theorem locatedInitialization_polynomial_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (sizes : InitializationRegister → Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat),
      (∀ r, cs r ≤ (sizes r).eval n) →
      locatedInitializationSteps header stackRank symbolCard symbolRank tm e a backward cs ≤ clock.eval n := by
  let preparedSizes := cellCoordinatePolynomials header stackRank symbolCard symbolRank sizes
  obtain ⟨clock, hc⟩ := initializationInputBody_polynomial_bound tm e a backward preparedSizes
  refine ⟨cellCoordinateClock header stackRank symbolCard symbolRank sizes + clock, ?_⟩
  intro n cs h
  have hprep : ∀ r, cellCoordinateResult header stackRank symbolCard symbolRank cs r ≤ (preparedSizes r).eval n := by
    intro r
    change cellCoordinateResult header stackRank symbolCard symbolRank cs r ≤
      (cellCoordinatePolynomials header stackRank symbolCard symbolRank sizes r).eval n
    rw [congrFun (cellCoordinatePolynomials_eval header stackRank symbolCard symbolRank sizes n) r]
    exact operationResult_mono _ _ _ (cleanupCounters_mono _ cs _ h) r
  have ha := Nat.add_le_add (cleanupSteps_mono [(Sum.inr 1 : InitializationRegister)] cs _ h)
    (operationSteps_mono (cellCoordinateOperations header stackRank symbolCard symbolRank) _ _
      (cleanupCounters_mono [(Sum.inr 1 : InitializationRegister)] cs _ h))
  rw [Polynomial.eval_add, cellCoordinateClock_eval]
  exact Nat.add_le_add ha (hc n _ hprep)

theorem locatedInitialization_preserves_remaining (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) :
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 11) = cs (.inr 11) := by
  rw [locatedInitializationCounters, initializationInputBodyCounters, fixedNodeCounters_other]
  · simp [initializationAddress_result, cellCoordinateResult_eq]
  all_goals simp [initializationNodeRegisters]

end ShiReversibleGenerator
