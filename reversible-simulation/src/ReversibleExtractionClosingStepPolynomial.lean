import ReversibleExtractionClosingStep
import ReversibleExtractionClosingAdvancePolynomial
import ReversibleExtractionBoundClosingBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

theorem extractionClosingStepTemplate_polynomial (tm : Turing.FinTM2) (backward : Bool)
    (bound : Polynomial Nat) : (extractionClosingStepTemplate tm backward).PolynomiallyTimed bound := by
  obtain ⟨middle,hbudget⟩ := extractionBoundClosingPrinterTemplate_budget tm backward bound
  apply sequenceProgramTemplate_polynomial _ _ bound middle
  · exact extractionBoundClosingPrinterTemplate_polynomial tm backward bound
  · intro n cs hb hr
    exact hbudget n cs hb
  · exact extractionClosingAdvanceTemplate_polynomial middle

end ShiReversibleGenerator
