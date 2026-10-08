import ReversibleExtractionClosingResources
import ReversibleFixedNodeProgramTemplateBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

theorem extractionBoundClosingPrinterTemplate_budget (tm : Turing.FinTM2) (backward : Bool)
    (bound : Polynomial Nat) : ∃ budget : Polynomial Nat,∀ n (cs : ExtractionTermRegister → Nat),
      (∀ q,cs q ≤ bound.eval n) → ∀ q,(extractionBoundClosingPrinterTemplate tm backward).counters cs q ≤ budget.eval n := by
  obtain ⟨middle,hclock,hsetup⟩ := extractionClosingSetupTemplate_resources tm bound
  obtain ⟨budget,hbudget⟩ := fixedNodeProgramTemplate_budget extractionTermNodeRegisters
    (extractionClosingPrinterTemplates backward (19 : ExtractionTermRegister) 21) middle
  refine ⟨budget,?_⟩
  intro n cs hb
  exact hbudget n _ (hsetup n cs hb)

end ShiReversibleGenerator
