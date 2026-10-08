import ReversibleExtractionInputBindingAgreement
import ReversibleCleanupProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Scratch cleanup, runtime index computation and concrete wire binding are actual finite instructions. -/
noncomputable def extractionInputSetupTemplate (tm : Turing.FinTM2) (stride : Nat) :=
  sequenceProgramTemplate (cleanupProgramTemplate [7,8])
    (sequenceProgramTemplate extractionIndexSetupTemplate
      (sequenceProgramTemplate (cleanupProgramTemplate [8]) (extractionInputBindingTemplate tm stride)))

theorem extractionInputSetupTemplate_embeds (tm : Turing.FinTM2) (stride : Nat) :
    (extractionInputSetupTemplate tm stride).Embeds := by
  unfold extractionInputSetupTemplate
  exact sequenceProgramTemplate_embeds _ _ (cleanupProgramTemplate_embeds [7,8])
    (sequenceProgramTemplate_embeds _ _ extractionIndexSetupTemplate_embeds
      (sequenceProgramTemplate_embeds _ _ (cleanupProgramTemplate_embeds [8])
        (extractionInputBindingTemplate_embeds tm stride)))

theorem extractionInputSetupTemplate_run (tm : Turing.FinTM2) (stride : Nat) :
    (extractionInputSetupTemplate tm stride).Runs := by
  unfold extractionInputSetupTemplate
  exact sequenceProgramTemplate_run _ _ (cleanupProgramTemplate_embeds [7,8])
    (cleanupProgramTemplate_run [7,8])
    (sequenceProgramTemplate_run _ _ extractionIndexSetupTemplate_embeds extractionIndexSetupTemplate_run
      (sequenceProgramTemplate_run _ _ (cleanupProgramTemplate_embeds [8])
        (cleanupProgramTemplate_run [8]) (extractionInputBindingTemplate_run tm stride)))

theorem extractionInputSetupTemplate_ready (tm : Turing.FinTM2) (stride : Nat)
    (cs : ExtractionTermRegister → Nat) : (extractionInputSetupTemplate tm stride).ready cs := by
  refine ⟨trivial,?_,trivial,?_⟩
  · apply extractionIndexSetupTemplate_ready
    simp [cleanupProgramTemplate,cleanupCounters_apply]
  · apply extractionInputBindingTemplate_ready
    · simp [cleanupProgramTemplate,cleanupCounters_apply]
    · rw [show (cleanupProgramTemplate [8]).counters
          (extractionIndexSetupTemplate.counters ((cleanupProgramTemplate [7,8]).counters cs)) 7=
        extractionIndexSetupTemplate.counters ((cleanupProgramTemplate [7,8]).counters cs) 7 by
          simp [cleanupProgramTemplate,cleanupCounters_apply]]
      rw [extractionIndexSetupTemplate_counters]
      simp [cleanupProgramTemplate,cleanupCounters_apply]

end ShiReversibleGenerator
