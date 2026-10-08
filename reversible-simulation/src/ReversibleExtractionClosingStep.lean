import ReversibleExtractionBoundClosingPayload
import ReversibleExtractionBoundClosingFrames
import ReversibleExtractionClosingAdvance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- One closing-pass iteration prints the three real nodes and advances the actual loop pointers. -/
noncomputable def extractionClosingStepTemplate (tm : Turing.FinTM2) (backward : Bool) :=
  sequenceProgramTemplate (extractionBoundClosingPrinterTemplate tm backward) extractionClosingAdvanceTemplate

theorem extractionClosingStepTemplate_embeds (tm : Turing.FinTM2) (backward : Bool) :
    (extractionClosingStepTemplate tm backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionBoundClosingPrinterTemplate_embeds tm backward)
    extractionClosingAdvanceTemplate_embeds

theorem extractionClosingStepTemplate_run (tm : Turing.FinTM2) (backward : Bool) :
    (extractionClosingStepTemplate tm backward).Runs :=
  sequenceProgramTemplate_run _ _ (extractionBoundClosingPrinterTemplate_embeds tm backward)
    (extractionBoundClosingPrinterTemplate_run tm backward) extractionClosingAdvanceTemplate_run

theorem extractionClosingStepTemplate_ready (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (hb : cs 17=0) : (extractionClosingStepTemplate tm backward).ready cs :=
  ⟨extractionBoundClosingPrinterTemplate_ready tm backward cs hb,
    extractionClosingAdvanceTemplate_ready _ (extractionBoundClosingPrinterTemplate_scratch tm backward cs)⟩

theorem extractionClosingStepTemplate_bytes (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) : (extractionClosingStepTemplate tm backward).bytes cs=
      (extractionBoundClosingPrinterTemplate tm backward).bytes cs := by
  simp [extractionClosingStepTemplate,sequenceProgramTemplate,extractionClosingAdvanceTemplate_bytes]

theorem extractionClosingStepTemplate_count (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) : (extractionClosingStepTemplate tm backward).counters cs 16=cs 16+41 := by
  change extractionClosingAdvanceTemplate.counters ((extractionBoundClosingPrinterTemplate tm backward).counters cs) 16=_
  rw [extractionClosingAdvanceTemplate_counters]
  simpa only [Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 21),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 20),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 19),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 18)] using
      extractionBoundClosingPrinterTemplate_count tm backward cs

end ShiReversibleGenerator
