import ReversibleLocatedConstantInitialization
import ReversibleFixedPrinterCounterPolynomials

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard symbolRank : Nat) (value backward : Bool)

noncomputable def locatedConstantCounterPolynomials (sizes : InitializationRegister → Polynomial Nat) :=
  fixedPrinterCounterPolynomials initializationNodeRegisters (constantInitializationTemplates value backward)
    (initializationPreparedPolynomials (cellCoordinatePolynomials header stackRank symbolCard symbolRank sizes))

theorem locatedConstantCounterPolynomials_eval (sizes : InitializationRegister → Polynomial Nat) (n : Nat) :
    (fun r => (locatedConstantCounterPolynomials header stackRank symbolCard symbolRank value backward sizes r).eval n) =
      locatedConstantCounters header stackRank symbolCard symbolRank value backward (fun r => (sizes r).eval n) := by
  rw [locatedConstantCounterPolynomials, fixedPrinterCounterPolynomials_eval,
    initializationPreparedPolynomials_eval, cellCoordinatePolynomials_eval]
  rfl

theorem locatedConstantCounters_mono (cs ds : InitializationRegister → Nat) (h : ∀ r, cs r ≤ ds r) :
    ∀ r, locatedConstantCounters header stackRank symbolCard symbolRank value backward cs r ≤
      locatedConstantCounters header stackRank symbolCard symbolRank value backward ds r := by
  apply fixedNodeCounters_mono
  apply operationResult_mono
  apply cleanupCounters_mono
  apply operationResult_mono
  exact cleanupCounters_mono _ cs ds h

end ShiReversibleGenerator
