import ReversibleExtractionClosingAdvance
import ReversibleCounterAffineExitBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionClosingAdvanceTemplate_polynomial (bound : Polynomial Nat) :
    extractionClosingAdvanceTemplate.PolynomiallyTimed bound := by
  unfold extractionClosingAdvanceTemplate
  apply sequenceProgramTemplate_polynomial _ _ bound (Polynomial.C 2*bound)
  · exact counterAffineAccumulationProgramTemplate_polynomial _ _ _
  · intro n cs hb hr q
    simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
      counterAffineUnitAccumulationProgramTemplate_budget (12 : ExtractionTermRegister) 18 7 cs (bound.eval n) hb q
  · apply sequenceProgramTemplate_polynomial _ _ (Polynomial.C 2*bound) (Polynomial.C 2*bound)
    · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
    · intro n cs hb hr
      exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
    · apply sequenceProgramTemplate_polynomial _ _ (Polynomial.C 2*bound) (Polynomial.C 2*bound)
      · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
      · intro n cs hb hr
        exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
      · apply sequenceProgramTemplate_polynomial _ _ (Polynomial.C 2*bound) (Polynomial.C 2*bound)
        · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
        · intro n cs hb hr
          exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
        · apply sequenceProgramTemplate_polynomial _ _ (Polynomial.C 2*bound) (Polynomial.C 2*bound)
          · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
          · intro n cs hb hr
            exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
          · exact counterAffineAccumulationProgramTemplate_polynomial _ _ _

end ShiReversibleGenerator
