import ReversibleExtractionMasterRegisterInjection
import ReversibleCounterPairRetreatBudget
import ReversibleCounterAffineOffsetCopyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def extractionResourceSetupPrograms (tm : Turing.FinTM2) (backward : Bool) :
    List (CounterProgramTemplate ExtractionMasterRegister) :=
  [cleanupProgramTemplate [.inl 5],
    counterAffineCopyProgramTemplate (.inl 2) (.inr 0) (.inl 5) 0 1 0,
    counterAffineCopyProgramTemplate (.inl 4) (.inr 27) (.inl 5) 0 1 0,
    decrementProgramTemplate (.inr 27),
    counterAffineCopyProgramTemplate (.inl 9) (.inr 26) (.inl 5) 0 1 0,
    counterAffineCopyProgramTemplate (.inl 11) (.inr 11) (.inl 5) 0 1 0,
    counterAffineCopyProgramTemplate (.inl 8) (.inr 8) (.inl 5) 0 1 0,
    counterPairRetreatTemplate (.inr 11) (.inr 25) (.inr 8),
    counterAffineAccumulationProgramTemplate ⟨.inl 0,.inr 11,tickSizeBound tm,0⟩ (.inl 5)] ++
  (if backward then [cleanupProgramTemplate [.inr 1],counterAffineCopyProgramTemplate (.inl 11) (.inr 18) (.inl 5) 0 1 0]
    else [counterAffineCopyProgramTemplate (.inl 9) (.inr 1) (.inl 5) 0 1 0,decrementProgramTemplate (.inr 1),
      counterAffineCopyProgramTemplate (.inl 10) (.inr 18) (.inl 5) 0 1 0]) ++
  [cleanupProgramTemplate (.inr 16 :: extractionForestScratch.map Sum.inr)]

/-- Resource metadata initializes the original final configuration source, slot direction and persistent padding bound. -/
noncomputable def extractionResourceSetupTemplate (tm : Turing.FinTM2) (backward : Bool) :=
  listProgramTemplate (extractionResourceSetupPrograms tm backward)

theorem extractionResourceSetupTemplate_embeds (tm : Turing.FinTM2) (backward : Bool) :
    (extractionResourceSetupTemplate tm backward).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  cases backward
  · simp only [extractionResourceSetupPrograms,Bool.false_eq_true,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl
    all_goals first | exact cleanupProgramTemplate_embeds _ | exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _ |
      exact decrementProgramTemplate_embeds _ | exact counterPairRetreatTemplate_embeds _ _ _ |
      exact counterAffineAccumulationProgramTemplate_embeds _ _
  · simp only [extractionResourceSetupPrograms,if_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl
    all_goals first | exact cleanupProgramTemplate_embeds _ | exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _ |
      exact decrementProgramTemplate_embeds _ | exact counterPairRetreatTemplate_embeds _ _ _ |
      exact counterAffineAccumulationProgramTemplate_embeds _ _

theorem extractionResourceSetupTemplate_run (tm : Turing.FinTM2) (backward : Bool) :
    (extractionResourceSetupTemplate tm backward).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    cases backward
    · simp only [extractionResourceSetupPrograms,Bool.false_eq_true,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl
      all_goals first | exact cleanupProgramTemplate_embeds _ | exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _ |
        exact decrementProgramTemplate_embeds _ | exact counterPairRetreatTemplate_embeds _ _ _ |
        exact counterAffineAccumulationProgramTemplate_embeds _ _
    · simp only [extractionResourceSetupPrograms,if_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl
      all_goals first | exact cleanupProgramTemplate_embeds _ | exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _ |
        exact decrementProgramTemplate_embeds _ | exact counterPairRetreatTemplate_embeds _ _ _ |
        exact counterAffineAccumulationProgramTemplate_embeds _ _
  · intro p hp
    cases backward
    · simp only [extractionResourceSetupPrograms,Bool.false_eq_true,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl
      all_goals first | exact cleanupProgramTemplate_run _ | (apply counterAffineCopyProgramTemplate_run <;> simp) |
        exact decrementProgramTemplate_run _ | exact counterPairRetreatTemplate_run _ _ _ |
        (apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid])
    · simp only [extractionResourceSetupPrograms,if_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl
      all_goals first | exact cleanupProgramTemplate_run _ | (apply counterAffineCopyProgramTemplate_run <;> simp) |
        exact decrementProgramTemplate_run _ | exact counterPairRetreatTemplate_run _ _ _ |
        (apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid])

end ShiReversibleGenerator
