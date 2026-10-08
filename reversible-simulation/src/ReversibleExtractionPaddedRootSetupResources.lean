import ReversibleExtractionPaddedRootSetup

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Every real root-setup counter, including arbitrary incoming scratch, stays polynomially bounded. -/
theorem extractionPaddedRootSetupTemplate_resources (bound : Polynomial Nat) :
    extractionPaddedRootSetupTemplate.CounterBound bound ∧ extractionPaddedRootSetupTemplate.PolynomiallyTimed bound := by
  have ha : ∀ source target : ExtractionPaddedRegister, ∀ b : Polynomial Nat,
      (counterAffineAccumulationProgramTemplate ⟨source,target,0,1⟩ 7).CounterBound b := by
    intro source target b
    refine ⟨Polynomial.C 2*b,?_⟩
    intro n cs hb q
    simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
      counterAffineUnitAccumulationProgramTemplate_budget source target 7 cs (b.eval n) hb q
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    simp only [extractionPaddedRootSetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact cleanupProgramTemplate_polynomial _ b
      | exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ b
      | exact counterAffineAccumulationProgramTemplate_polynomial _ _ b
      | exact decrementProgramTemplate_polynomial _ b
  · intro p hp b
    simp only [extractionPaddedRootSetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨b,by intro n cs hb q; exact cleanupCounters_uniform_bound _ cs _ hb q⟩
    all_goals first
      | exact counterAffineOffsetCopyProgramTemplate_budget _ _ _ _ _ b
      | exact ha _ _ b
      | refine ⟨b,?_⟩; intro n cs hb q; simp only [decrementProgramTemplate,Function.update_apply]; split_ifs <;> have hq := hb q <;> have ht := hb 24 <;> omega

end ShiReversibleGenerator
