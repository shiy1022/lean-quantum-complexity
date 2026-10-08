import ReversibleExtractionTermNegationCertificate
import ReversibleCounterAffineExitBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionTermNegationSetupTemplate_polynomial (bound : Polynomial Nat) :
    extractionTermNegationSetupTemplate.PolynomiallyTimed bound := by
  unfold extractionTermNegationSetupTemplate
  apply sequenceProgramTemplate_polynomial _ _ bound bound
  · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
  · intro n cs hb hr
    exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
  · apply sequenceProgramTemplate_polynomial _ _ bound (Polynomial.C 2*bound)
    · exact counterAffineAccumulationProgramTemplate_polynomial _ _ _
    · intro n cs hb hr q
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
        counterAffineUnitAccumulationProgramTemplate_budget (12 : ExtractionTermRegister) 21 7 cs (bound.eval n) hb q
    · apply sequenceProgramTemplate_polynomial _ _ (Polynomial.C 2*bound) (Polynomial.C 2*bound)
      · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
      · intro n cs hb hr
        exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
      · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _

theorem extractionTermNegationSetupTemplate_budget (bound : Polynomial Nat)
    (n : Nat) (cs : ExtractionTermRegister → Nat) (hb : ∀ q,cs q ≤ bound.eval n) :
    ∀ q,extractionTermNegationSetupTemplate.counters cs q ≤
      (Polynomial.C 2*bound+Polynomial.C 1).eval n := by
  intro q
  have hb18 := hb 18
  have hb12 := hb 12
  have hbq := hb q
  simp only [extractionTermNegationSetupTemplate_counters,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Function.update_apply]
  split_ifs <;> omega

/-- The real negation printer includes pointer binding in its polynomial instruction clock. -/
theorem extractionTermNegationPrinterTemplate_polynomial (backward : Bool) (bound : Polynomial Nat) :
    (extractionTermNegationPrinterTemplate backward).PolynomiallyTimed bound := by
  apply sequenceProgramTemplate_polynomial _ _ bound (Polynomial.C 2*bound+Polynomial.C 1)
  · exact extractionTermNegationSetupTemplate_polynomial bound
  · intro n cs hb hr
    exact extractionTermNegationSetupTemplate_budget bound n cs hb
  · exact fixedNodeProgramTemplate_polynomial _ _ _

end ShiReversibleGenerator
