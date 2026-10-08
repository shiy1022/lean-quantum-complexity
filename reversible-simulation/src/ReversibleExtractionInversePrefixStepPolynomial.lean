import ReversibleExtractionInversePrefixStepReady
import ReversibleCounterRunExitBudget
import ReversibleExtractionTermSizeResources
import ReversibleExtractionTermNegationResources

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Every actual inverse-prefix component, including pointer/index binding and cleanup, has a polynomial clock. -/
theorem extractionInversePrefixStepTemplate_polynomial (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    (extractionInversePrefixStepTemplate tm e stride).PolynomiallyTimed bound := by
  have hsize := extractionTermSizeProgramTemplate_polynomial tm bound
  obtain ⟨sizeBudget,sizeExit⟩ := CounterProgramTemplate.ready_exit_budget _
    (extractionTermSizeProgramTemplate_run tm) bound hsize
  have hterm := extractionBoundTermPrinterTemplate_polynomial tm e stride true sizeBudget
  obtain ⟨termBudget,termExit⟩ := CounterProgramTemplate.ready_exit_budget _
    (extractionBoundTermPrinterTemplate_run tm e stride true) sizeBudget hterm
  have hneg := extractionTermNegationPrinterTemplate_polynomial true termBudget
  obtain ⟨negBudget,negExit⟩ := CounterProgramTemplate.ready_exit_budget _
    (extractionTermNegationPrinterTemplate_run true) termBudget hneg
  unfold extractionInversePrefixStepTemplate
  apply sequenceProgramTemplate_polynomial _ _ bound sizeBudget hsize sizeExit
  apply sequenceProgramTemplate_polynomial _ _ sizeBudget termBudget hterm termExit
  exact sequenceProgramTemplate_polynomial _ _ termBudget negBudget hneg negExit
    (extractionPrefixAdvanceTemplate_polynomial negBudget)

end ShiReversibleGenerator
