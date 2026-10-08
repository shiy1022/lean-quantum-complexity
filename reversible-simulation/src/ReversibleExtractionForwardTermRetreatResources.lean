import ReversibleExtractionForwardTermRetreatCounters
import ReversibleExtractionTermSizeBudget
import ReversibleCounterPairRetreatBudget
import ReversibleCounterAffineExitBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionForwardTermRetreatTemplate_resources (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,(extractionForwardTermRetreatTemplate tm).PolynomiallyTimed bound ∧
      ∀ n (cs : ExtractionTermRegister → Nat),(∀ q,cs q ≤ bound.eval n) →
        ∀ q,(extractionForwardTermRetreatTemplate tm).counters cs q ≤ budget.eval n := by
  let middle := Polynomial.C 2*bound+Polynomial.C (10+Fintype.card (Option (MachineSymbol tm))*7)
  refine ⟨middle,?_,?_⟩
  · unfold extractionForwardTermRetreatTemplate
    apply sequenceProgramTemplate_polynomial _ _ bound middle
    · exact extractionTermSizeProgramTemplate_polynomial tm bound
    · intro n cs hb hr
      exact extractionTermSizeProgramTemplate_budget tm bound n cs hb
    · apply sequenceProgramTemplate_polynomial _ _ middle middle
      · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
      · intro n cs hb hr
        exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
      · exact counterPairRetreatTemplate_polynomial _ _ _ _
  · intro n cs hb
    have h0 := extractionTermSizeProgramTemplate_budget tm bound n cs hb
    have h1 := counterAffineUnitCopyProgramTemplate_budget (12 : ExtractionTermRegister) 8 7 3 _ _ h0
    exact counterPairRetreatTemplate_budget 18 20 8 (by decide) (by decide) (by decide) _ _ h1

end ShiReversibleGenerator
