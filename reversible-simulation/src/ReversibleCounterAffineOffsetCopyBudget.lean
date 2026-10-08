import ReversibleCounterAffineExitBounds
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem counterAffineOffsetCopyProgramTemplate_budget (source target tmp : R) (positive negative : Nat)
    (bound : Polynomial Nat) :
    (counterAffineCopyProgramTemplate source target tmp positive 1 negative).CounterBound bound := by
  refine ⟨bound+Polynomial.C positive,?_⟩
  intro n cs hb q
  have hs := hb source
  have hq := hb q
  simp only [counterAffineCopyProgramTemplate,Polynomial.eval_add,Polynomial.eval_C,Function.update_apply]
  split_ifs <;> omega

end ShiReversibleGenerator
