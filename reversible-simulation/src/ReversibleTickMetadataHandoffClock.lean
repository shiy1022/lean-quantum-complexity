import ReversibleTickMetadataHandoffTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The four metadata copies and five cleanups retain a common bound on every runtime counter. -/
theorem tickMetadataHandoffTemplate_uniform_bound (tm : Turing.FinTM2) (budget : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hb : ∀ q,cs q ≤ budget) :
    ∀ q,(tickMetadataHandoffTemplate tm).counters cs q ≤ budget := by
  intro q
  have h0 := hb (.inl 0)
  have h1 := hb (.inl 1)
  have h2 := hb (.inl 2)
  have h11 := hb (.inl 11)
  have hq := hb q
  simp [tickMetadataHandoffTemplate,tickMetadataHandoffPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,
    Function.update_apply,tickTraversalSpare]
  split_ifs <;> omega

/-- The actual handoff cost is bounded by 46 times the register budget plus17 instructions. -/
theorem tickMetadataHandoffTemplate_polynomial (tm : Turing.FinTM2) (budget : Polynomial Nat) :
    (tickMetadataHandoffTemplate tm).PolynomiallyTimed budget := by
  refine ⟨Polynomial.C 46*budget+Polynomial.C 17,?_⟩
  intro n cs hb _
  have h0 := hb (.inl 0)
  have h1 := hb (.inl 1)
  have h2 := hb (.inl 2)
  have h3 := hb (.inl 3)
  have h4 := hb (.inl 4)
  have h9 := hb (.inl 9)
  have h10 := hb (.inl 10)
  have h11 := hb (.inl 11)
  have hs1 := hb (tickTraversalSpare tm 1)
  have hs6 := hb (tickTraversalSpare tm 6)
  have hs7 := hb (tickTraversalSpare tm 7)
  simp [tickMetadataHandoffTemplate,tickMetadataHandoffPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate,cleanupSteps,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,tickTraversalSpare] at ⊢
  simp [tickTraversalSpare] at hs1 hs6 hs7
  omega

end ShiReversibleGenerator
