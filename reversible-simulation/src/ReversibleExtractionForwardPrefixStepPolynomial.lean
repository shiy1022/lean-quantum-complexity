import ReversibleExtractionForwardPrefixStepReady
import ReversibleExtractionForwardTermRetreatResources
import ReversibleExtractionTermNegationBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionForwardPrefixStepTemplate_polynomial (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).PolynomiallyTimed bound := by
  obtain ⟨middle,hretreat,hretreatBudget⟩ := extractionForwardTermRetreatTemplate_resources tm bound
  obtain ⟨final,hnegBudget⟩ := extractionTermNegationPrinterTemplate_budget false middle
  unfold extractionForwardPrefixStepTemplate
  apply sequenceProgramTemplate_polynomial _ _ bound middle
  · exact hretreat
  · intro n cs hb hr
    exact hretreatBudget n cs hb
  · apply sequenceProgramTemplate_polynomial _ _ middle final
    · exact extractionTermNegationPrinterTemplate_polynomial false middle
    · intro n cs hb hr
      exact hnegBudget n cs hb
    · obtain ⟨clock,hclock⟩ := extractionBoundTermPrinterTemplate_polynomial tm e stride false final
      refine ⟨clock+Polynomial.C 1,?_⟩
      intro n cs hb hr
      simpa only [sequenceProgramTemplate,decrementProgramTemplate,Polynomial.eval_add,Polynomial.eval_C] using
        Nat.add_le_add_right (hclock n cs hb hr.1) 1

end ShiReversibleGenerator
