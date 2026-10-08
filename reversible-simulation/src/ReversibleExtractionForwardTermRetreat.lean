import ReversibleExtractionTermSizeResources
import ReversibleCounterPairRetreat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Starting at the final false node, compute the real selected term size and retreat to its original base. -/
noncomputable def extractionForwardTermRetreatTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (extractionTermSizeProgramTemplate tm)
    (sequenceProgramTemplate (counterAffineCopyProgramTemplate 12 8 7 0 1 3)
      (counterPairRetreatTemplate 18 20 8))

theorem extractionForwardTermRetreatTemplate_embeds (tm : Turing.FinTM2) :
    (extractionForwardTermRetreatTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionTermSizeProgramTemplate_embeds tm)
    (sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (counterPairRetreatTemplate_embeds _ _ _))

theorem extractionForwardTermRetreatTemplate_run (tm : Turing.FinTM2) :
    (extractionForwardTermRetreatTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (extractionTermSizeProgramTemplate_embeds tm) (extractionTermSizeProgramTemplate_run tm)
    (sequenceProgramTemplate_run _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide))
      (counterPairRetreatTemplate_run _ _ _))

theorem extractionForwardTermRetreatTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardTermRetreatTemplate tm).ready cs := by
  refine ⟨extractionTermSizeProgramTemplate_ready tm cs,?_,?_⟩
  · simp [counterAffineCopyProgramTemplate,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  · exact counterPairRetreatTemplate_ready _ _ _ (by decide) (by decide) _

theorem extractionForwardTermRetreatTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardTermRetreatTemplate tm).bytes cs=[] := by
  simp [extractionForwardTermRetreatTemplate,sequenceProgramTemplate,extractionTermSizeProgramTemplate_bytes,
    counterAffineCopyProgramTemplate,counterPairRetreatTemplate_bytes]

end ShiReversibleGenerator
