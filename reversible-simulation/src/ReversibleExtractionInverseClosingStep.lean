import ReversibleExtractionInverseClosingRetreatMetadata
import ReversibleExtractionInverseClosingAdvance
import ReversibleExtractionBoundClosingPayload
import ReversibleExtractionBoundClosingFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The real inverse closing iteration retreats the term base, prints inverse nodes, then advances the suffix. -/
noncomputable def extractionInverseClosingStepTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (extractionInverseClosingRetreatTemplate tm)
    (sequenceProgramTemplate (extractionBoundClosingPrinterTemplate tm true) extractionInverseClosingAdvanceTemplate)

theorem extractionInverseClosingStepTemplate_embeds (tm : Turing.FinTM2) :
    (extractionInverseClosingStepTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionInverseClosingRetreatTemplate_embeds tm)
    (sequenceProgramTemplate_embeds _ _ (extractionBoundClosingPrinterTemplate_embeds tm true)
      extractionInverseClosingAdvanceTemplate_embeds)

theorem extractionInverseClosingStepTemplate_run (tm : Turing.FinTM2) :
    (extractionInverseClosingStepTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (extractionInverseClosingRetreatTemplate_embeds tm)
    (extractionInverseClosingRetreatTemplate_run tm)
    (sequenceProgramTemplate_run _ _ (extractionBoundClosingPrinterTemplate_embeds tm true)
      (extractionBoundClosingPrinterTemplate_run tm true) extractionInverseClosingAdvanceTemplate_run)

theorem extractionInverseClosingStepTemplate_ready (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (hb : cs 17=0) :
    (extractionInverseClosingStepTemplate tm).ready cs := by
  refine ⟨extractionInverseClosingRetreatTemplate_ready tm cs,?_,?_⟩
  · apply extractionBoundClosingPrinterTemplate_ready tm true
    exact (extractionInverseClosingRetreatTemplate_frame tm cs 17
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
  · exact extractionInverseClosingAdvanceTemplate_ready _
      (extractionBoundClosingPrinterTemplate_scratch tm true _)

theorem extractionInverseClosingStepTemplate_bytes (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingStepTemplate tm).bytes cs=
      (extractionBoundClosingPrinterTemplate tm true).bytes
        ((extractionInverseClosingRetreatTemplate tm).counters cs) := by
  simp [extractionInverseClosingStepTemplate,sequenceProgramTemplate,
    extractionInverseClosingRetreatTemplate_bytes,extractionInverseClosingAdvanceTemplate_bytes]

end ShiReversibleGenerator
