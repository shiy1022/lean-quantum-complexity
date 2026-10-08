import ReversibleExtractionClosingSetupCounters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Term-size computation and both closing-wire bindings precede the actual closing-node printer. -/
noncomputable def extractionBoundClosingPrinterTemplate (tm : Turing.FinTM2) (backward : Bool) :=
  sequenceProgramTemplate (extractionClosingSetupTemplate tm)
    (extractionClosingPrinterTemplate backward 19 21 extractionTermNodeRegisters)

theorem extractionBoundClosingPrinterTemplate_embeds (tm : Turing.FinTM2) (backward : Bool) :
    (extractionBoundClosingPrinterTemplate tm backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionClosingSetupTemplate_embeds tm)
    (extractionClosingPrinterTemplate_embeds _ _ _ _)

theorem extractionBoundClosingPrinterTemplate_run (tm : Turing.FinTM2) (backward : Bool) :
    (extractionBoundClosingPrinterTemplate tm backward).Runs :=
  sequenceProgramTemplate_run _ _ (extractionClosingSetupTemplate_embeds tm)
    (extractionClosingSetupTemplate_run tm)
    (extractionClosingPrinterTemplate_run backward 19 21 extractionTermNodeRegisters
      (by simp [extractionTermNodeRegisters,NodePrinterRegisters.Valid])
      (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable])
      (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]))

theorem extractionBoundClosingPrinterTemplate_ready (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (hb : cs 17=0) :
    (extractionBoundClosingPrinterTemplate tm backward).ready cs := by
  refine ⟨extractionClosingSetupTemplate_ready tm cs,?_⟩
  change ((extractionClosingSetupTemplate tm).counters cs) 17=0 ∧
    ((extractionClosingSetupTemplate tm).counters cs) 7=0
  rw [extractionClosingSetupTemplate_counters]
  simp [extractionTermSizeProgramTemplate_counters,cleanupCounters_apply,hb]

end ShiReversibleGenerator
