import ReversibleTickInitializedWindowTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Runtime initialized-slice pointer setup has an actual polynomial instruction bound. -/
theorem tickInitializedWindowTemplate_polynomial (tm : Turing.FinTM2) (budget : Polynomial Nat) :
    (tickInitializedWindowTemplate tm).PolynomiallyTimed budget := by
  let coefficient := 18*tickWidthSlope tm
  refine ⟨Polynomial.C (18+7*coefficient)*budget+
    Polynomial.C (23+2*coefficient+18*tickWidthOffset tm),?_⟩
  intro n cs hb _
  have h0 := hb (.inl 0)
  have hout := hb (tickTraversalSpare tm 2)
  have hraw := hb (tickTraversalSpare tm 6)
  have hcap := Nat.mul_le_mul_left (7*coefficient) (hb (.inl 1))
  simp [tickInitializedWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.steps,tickInitializedWindowAtom,tickTraversalSpare,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] at ⊢
  simp [tickTraversalSpare,coefficient] at hout hraw hcap ⊢
  nlinarith

end ShiReversibleGenerator
