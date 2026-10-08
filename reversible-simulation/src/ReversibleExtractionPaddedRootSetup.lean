import ReversibleExtractionPaddedRootCopy
import ReversibleCounterAffineOffsetCopyBudget
import ReversibleDecrementProgramTemplate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Register4 contains the runtime padding bound and register12 the computed exact formula size. -/
noncomputable def extractionPaddedRootSetupPrograms : List (CounterProgramTemplate ExtractionPaddedRegister) :=
  [cleanupProgramTemplate [2,7,17],
   counterAffineCopyProgramTemplate 18 24 7 0 1 0,
   counterAffineAccumulationProgramTemplate ⟨12,24,0,1⟩ 7,
   decrementProgramTemplate 24,
   counterAffineCopyProgramTemplate 24 20 7 0 1 0,
   counterAffineCopyProgramTemplate 18 25 7 0 1 0,
   counterAffineAccumulationProgramTemplate ⟨4,25,0,1⟩ 7,
   counterAffineCopyProgramTemplate 0 9 7 1 1 0,
   counterAffineCopyProgramTemplate 0 22 7 1 1 0]

noncomputable def extractionPaddedRootSetupTemplate := listProgramTemplate extractionPaddedRootSetupPrograms

theorem extractionPaddedRootSetupTemplate_embeds : extractionPaddedRootSetupTemplate.Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [extractionPaddedRootSetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact cleanupProgramTemplate_embeds _
    | exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    | exact counterAffineAccumulationProgramTemplate_embeds _ _
    | exact decrementProgramTemplate_embeds _

theorem extractionPaddedRootSetupTemplate_run : extractionPaddedRootSetupTemplate.Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [extractionPaddedRootSetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact cleanupProgramTemplate_embeds _
      | exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
      | exact counterAffineAccumulationProgramTemplate_embeds _ _
      | exact decrementProgramTemplate_embeds _
  · intro p hp
    simp only [extractionPaddedRootSetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact cleanupProgramTemplate_run _
      | exact counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide)
      | (apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid])
      | exact decrementProgramTemplate_run (24 : ExtractionPaddedRegister)

theorem extractionPaddedRootSetupTemplate_ready (cs : ExtractionPaddedRegister → Nat) :
    extractionPaddedRootSetupTemplate.ready cs := by
  simp [extractionPaddedRootSetupTemplate,extractionPaddedRootSetupPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,
    counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,AffineAtom.apply,decrementProgramTemplate]

theorem extractionPaddedRootSetupTemplate_bytes (cs : ExtractionPaddedRegister → Nat) :
    extractionPaddedRootSetupTemplate.bytes cs=[] := by
  simp [extractionPaddedRootSetupTemplate,extractionPaddedRootSetupPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,decrementProgramTemplate]

theorem extractionPaddedRootSetupTemplate_counters (cs : ExtractionPaddedRegister → Nat) :
    extractionPaddedRootSetupTemplate.counters cs=
      Function.update (Function.update (Function.update (Function.update (Function.update
        (cleanupCounters [2,7,17] cs) 24 (cs 18+cs 12-1)) 20 (cs 18+cs 12-1))
          25 (cs 18+cs 4)) 9 (cs 0+1)) 22 (cs 0+1) := by
  simp [extractionPaddedRootSetupTemplate,extractionPaddedRootSetupPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,
    counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,AffineAtom.apply,
    decrementProgramTemplate,Nat.add_comm]

end ShiReversibleGenerator
