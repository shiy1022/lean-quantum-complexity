import ReversibleExtractionTermSizeResources
import ReversibleCounterPairRetreat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Inverse closing retreats to the selected term while preserving the moving closing endpoint20. -/
noncomputable def extractionInverseClosingRetreatTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (extractionTermSizeProgramTemplate tm)
    (sequenceProgramTemplate (counterAffineCopyProgramTemplate 12 8 7 0 1 3)
      (counterPairRetreatTemplate 18 19 8))

theorem extractionInverseClosingRetreatTemplate_embeds (tm : Turing.FinTM2) :
    (extractionInverseClosingRetreatTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionTermSizeProgramTemplate_embeds tm)
    (sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (counterPairRetreatTemplate_embeds _ _ _))

theorem extractionInverseClosingRetreatTemplate_run (tm : Turing.FinTM2) :
    (extractionInverseClosingRetreatTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (extractionTermSizeProgramTemplate_embeds tm) (extractionTermSizeProgramTemplate_run tm)
    (sequenceProgramTemplate_run _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide))
      (counterPairRetreatTemplate_run _ _ _))

theorem extractionInverseClosingRetreatTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingRetreatTemplate tm).ready cs := by
  refine ⟨extractionTermSizeProgramTemplate_ready tm cs,?_,?_⟩
  · simp [counterAffineCopyProgramTemplate,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  · exact counterPairRetreatTemplate_ready _ _ _ (by decide) (by decide) _

theorem extractionInverseClosingRetreatTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingRetreatTemplate tm).bytes cs=[] := by
  simp [extractionInverseClosingRetreatTemplate,sequenceProgramTemplate,extractionTermSizeProgramTemplate_bytes,
    counterAffineCopyProgramTemplate,counterPairRetreatTemplate_bytes]

end ShiReversibleGenerator
