import ReversibleExtractionResourceSetupMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator

theorem extractionResourceSetupTemplate_resources (tm : Turing.FinTM2) (backward : Bool) (bound : Polynomial Nat) :
    (extractionResourceSetupTemplate tm backward).CounterBound bound ∧
      (extractionResourceSetupTemplate tm backward).PolynomiallyTimed bound := by
  have hd : ∀ (r : ExtractionMasterRegister) (b : Polynomial Nat),(decrementProgramTemplate r).CounterBound b := by
    intro r b
    refine ⟨b,?_⟩
    intro n cs hb q
    have hq := hb q
    have hr := hb r
    simp only [decrementProgramTemplate,Function.update_apply]
    split_ifs <;> omega
  have ha : ∀ (a : AffineAtom ExtractionMasterRegister) (tmp : ExtractionMasterRegister) (b : Polynomial Nat),
      (counterAffineAccumulationProgramTemplate a tmp).CounterBound b := by
    intro a tmp b
    refine ⟨Polynomial.C (a.coefficient+1)*b+Polynomial.C a.offset,?_⟩
    intro n cs hb q
    have hs := hb a.source
    have ht := hb a.target
    have hq := hb q
    simp only [counterAffineAccumulationProgramTemplate,AffineAtom.apply,Function.update_apply,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    split_ifs <;> nlinarith
  have hcl : ∀ (clear : List ExtractionMasterRegister) (b : Polynomial Nat),
      (cleanupProgramTemplate clear).CounterBound b := by
    intro clear b
    exact ⟨b,by intro n cs hb q; exact cleanupCounters_uniform_bound clear cs _ hb q⟩
  have hpair : ∀ b : Polynomial Nat,
      (counterPairRetreatTemplate (Sum.inr 11 : ExtractionMasterRegister) (.inr 25) (.inr 8)).CounterBound b := by
    intro b
    exact ⟨b,by intro n cs hb q; exact counterPairRetreatTemplate_budget _ _ _ (by decide) (by decide) (by decide) cs (b.eval n) hb q⟩
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    cases backward
    · simp only [extractionResourceSetupPrograms,Bool.false_eq_true,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl
      all_goals first | exact cleanupProgramTemplate_polynomial _ b | exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ b |
        exact decrementProgramTemplate_polynomial _ b | exact counterPairRetreatTemplate_polynomial _ _ _ b |
        exact counterAffineAccumulationProgramTemplate_polynomial _ _ b
    · simp only [extractionResourceSetupPrograms,if_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl
      all_goals first | exact cleanupProgramTemplate_polynomial _ b | exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ b |
        exact decrementProgramTemplate_polynomial _ b | exact counterPairRetreatTemplate_polynomial _ _ _ b |
        exact counterAffineAccumulationProgramTemplate_polynomial _ _ b
  · intro p hp b
    cases backward
    · simp only [extractionResourceSetupPrograms,Bool.false_eq_true,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl
      all_goals first | exact hcl _ b | exact counterAffineOffsetCopyProgramTemplate_budget _ _ _ _ _ b | exact hd _ b | exact hpair b | exact ha _ _ b
    · simp only [extractionResourceSetupPrograms,if_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl
      all_goals first | exact hcl _ b | exact counterAffineOffsetCopyProgramTemplate_budget _ _ _ _ _ b | exact hd _ b | exact hpair b | exact ha _ _ b

end ShiReversibleGenerator
