import ReversibleExtractionInputSetupAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Every selected term's input setup and runtime dispatch belong to one actual finite graph. -/
noncomputable def extractionBoundTermPrinterTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) :=
  sequenceProgramTemplate (extractionInputSetupTemplate tm stride)
    (extractionTermDispatchTemplate tm e backward (extractionBoundInputs tm stride))

theorem extractionBoundTermPrinterTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionBoundTermPrinterTemplate tm e stride backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionInputSetupTemplate_embeds tm stride)
    (extractionTermDispatchTemplate_embeds tm e backward _)

theorem extractionBoundTermPrinterTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionBoundTermPrinterTemplate tm e stride backward).Runs :=
  sequenceProgramTemplate_run _ _ (extractionInputSetupTemplate_embeds tm stride)
    (extractionInputSetupTemplate_run tm stride)
    (extractionTermDispatchTemplate_run tm e backward _ (extractionBoundInputs_stable tm stride))

/-- Every runtime parameter and printer count survives input setup. -/
theorem extractionInputSetupTemplate_frame (tm : Turing.FinTM2) (stride : Nat)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h7 : q ≠ 7) (h8 : q ≠ 8) (h9 : q ≠ 9) (h4 : q ≠ 4) (h10 : q ≠ 10)
    (h19 : q ≠ 19) (h20 : q ≠ 20) (h21 : q ≠ 21) :
    (extractionInputSetupTemplate tm stride).counters cs q=cs q := by
  simp [extractionInputSetupTemplate,sequenceProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,
    extractionIndexSetupTemplate_counters,extractionInputBindingTemplate,coordinateBindingProgramTemplate,
    extractionInputBindingRegisters,h7,h8,h9,h4,h10,h19,h20,h21]

theorem extractionInputSetupTemplate_bytes (tm : Turing.FinTM2) (stride : Nat)
    (cs : ExtractionTermRegister → Nat) : (extractionInputSetupTemplate tm stride).bytes cs=[] := by
  simp [extractionInputSetupTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    extractionIndexSetupTemplate_bytes,extractionInputBindingTemplate,coordinateBindingProgramTemplate]

end ShiReversibleGenerator
