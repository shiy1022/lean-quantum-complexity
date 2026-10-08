import ReversibleExtractionInputBindingResources
import ReversibleExtractionIndexSetupBudget
import ReversibleExtractionInputSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The actual setup preserves a polynomial bound on every counter, and has a polynomial clock. -/
theorem extractionInputSetupTemplate_resources (tm : Turing.FinTM2) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, (extractionInputSetupTemplate tm stride).PolynomiallyTimed bound ∧
      ∀ n (cs : ExtractionTermRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
        ∀ q,(extractionInputSetupTemplate tm stride).counters cs q ≤ budget.eval n := by
  obtain ⟨budget,clock,hbinding⟩ := extractionInputBindingTemplate_resources tm stride bound
  have hcleanup : ∀ n (cs : ExtractionTermRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
      ∀ q,(cleanupProgramTemplate [7,8]).counters cs q ≤ bound.eval n := by
    intro n cs hb
    exact cleanupCounters_uniform_bound _ cs _ hb
  have hindex : ∀ n (cs : ExtractionTermRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
      ∀ q,extractionIndexSetupTemplate.counters cs q ≤ bound.eval n := by
    intro n cs hb
    exact extractionIndexSetupTemplate_budget cs _ hb
  have hclear8 : ∀ n (cs : ExtractionTermRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
      ∀ q,(cleanupProgramTemplate [8]).counters cs q ≤ bound.eval n := by
    intro n cs hb
    exact cleanupCounters_uniform_bound _ cs _ hb
  refine ⟨budget,?_,?_⟩
  · unfold extractionInputSetupTemplate
    apply sequenceProgramTemplate_polynomial _ _ bound bound
    · exact cleanupProgramTemplate_polynomial _ _
    · intro n cs hb hr
      exact hcleanup n cs hb
    · apply sequenceProgramTemplate_polynomial _ _ bound bound
      · exact extractionIndexSetupTemplate_polynomial bound
      · intro n cs hb hr
        exact hindex n cs hb
      · apply sequenceProgramTemplate_polynomial _ _ bound bound
        · exact cleanupProgramTemplate_polynomial _ _
        · intro n cs hb hr
          exact hclear8 n cs hb
        · exact extractionInputBindingTemplate_polynomial tm stride bound
  · intro n cs hb q
    exact (hbinding n _ (hclear8 n _ (hindex n _ (hcleanup n cs hb)))).1 q

end ShiReversibleGenerator
