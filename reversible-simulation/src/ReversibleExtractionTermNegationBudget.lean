import ReversibleExtractionTermNegationResources
import ReversibleFixedNodeProgramTemplateBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

theorem extractionTermNegationPrinterTemplate_budget (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,∀ n (cs : ExtractionTermRegister → Nat),(∀ q,cs q ≤ bound.eval n) →
      ∀ q,(extractionTermNegationPrinterTemplate backward).counters cs q ≤ budget.eval n := by
  obtain ⟨budget,hbudget⟩ := fixedNodeProgramTemplate_budget extractionTermNodeRegisters
    [symbolicAssignmentTemplate backward (.neg ⟨19,0⟩ ⟨21,0⟩)] (Polynomial.C 2*bound+Polynomial.C 1)
  refine ⟨budget,?_⟩
  intro n cs hb
  exact hbudget n _ (extractionTermNegationSetupTemplate_budget bound n cs hb)

end ShiReversibleGenerator
