import ReversibleExtractionWholeSizeProgram
import ReversibleCounterRunExitBudget
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The always-ready whole-size program has unconditional polynomial bounds for every real exit counter. -/
theorem extractionWholeSizeProgramTemplate_resources (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionWholeSizeProgramTemplate tm).CounterBound bound ∧
      (extractionWholeSizeProgramTemplate tm).PolynomiallyTimed bound := by
  have ht := extractionWholeSizeProgramTemplate_polynomial tm bound
  obtain ⟨budget,hbudget⟩ := CounterProgramTemplate.ready_exit_budget
    (extractionWholeSizeProgramTemplate tm) (extractionWholeSizeProgramTemplate_run tm) bound ht
  exact ⟨⟨budget,fun n cs hb q => hbudget n cs hb (extractionWholeSizeProgramTemplate_ready tm cs) q⟩,ht⟩

end ShiReversibleGenerator
