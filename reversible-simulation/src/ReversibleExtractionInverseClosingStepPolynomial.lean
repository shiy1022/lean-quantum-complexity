import ReversibleExtractionInverseClosingStep
import ReversibleExtractionInverseClosingRetreatResources
import ReversibleExtractionBoundClosingBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Polynomial time comes from the actual retreat, actual node printer and actual advance graph. -/
theorem extractionInverseClosingStepTemplate_polynomial (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionInverseClosingStepTemplate tm).PolynomiallyTimed bound := by
  obtain ⟨middle,hretreat,hexit⟩ := extractionInverseClosingRetreatTemplate_resources tm bound
  obtain ⟨last,hlast⟩ := extractionBoundClosingPrinterTemplate_budget tm true middle
  apply sequenceProgramTemplate_polynomial _ _ bound middle
  · exact hretreat
  · intro n cs hb hr
    exact hexit n cs hb
  · apply sequenceProgramTemplate_polynomial _ _ middle last
    · exact extractionBoundClosingPrinterTemplate_polynomial tm true middle
    · intro n cs hb hr
      exact hlast n cs hb
    · exact extractionInverseClosingAdvanceTemplate_polynomial last

end ShiReversibleGenerator
