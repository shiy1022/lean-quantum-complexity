import ReversibleExtractionSizeStepClock
import ReversibleExtractionTermDispatch
import ReversibleTemplateRegisterInjectionRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The runtime size accumulator occupies register12; input-address and layer-count registers are framed. -/
def extractionSizeToTermRegister (i : ExtractionSizeRegister) : ExtractionTermRegister :=
  ⟨if i.val=4 then 12 else i.val,by split_ifs <;> omega⟩

theorem extractionSizeToTermRegister_injective : Function.Injective extractionSizeToTermRegister := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [extractionSizeToTermRegister] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

noncomputable def extractionTermSizeProgramTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (cleanupProgramTemplate [12,5,6,7])
    (injectProgramTemplate (extractionSizeStepTemplate tm) extractionSizeToTermRegister 2)

theorem extractionTermSizeProgramTemplate_embeds (tm : Turing.FinTM2) :
    (extractionTermSizeProgramTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (cleanupProgramTemplate_embeds _)
    (injectProgramTemplate_embeds _ _ _)

theorem extractionTermSizeProgramTemplate_run (tm : Turing.FinTM2) :
    (extractionTermSizeProgramTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (cleanupProgramTemplate_embeds _) (cleanupProgramTemplate_run _)
    (injectProgramTemplate_run _ _ extractionSizeToTermRegister_injective _
      (extractionSizeStepTemplate_embeds tm) (extractionSizeStepTemplate_run tm))

theorem extractionTermSizeProgramTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionTermSizeProgramTemplate tm).ready cs := by
  refine ⟨trivial,?_⟩
  change (extractionSizeStepTemplate tm).ready _
  rw [extractionSizeStepTemplate_ready]
  simp [extractionSizeToTermRegister,cleanupProgramTemplate,cleanupCounters_apply]

theorem extractionTermSizeProgramTemplate_value (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionTermSizeProgramTemplate tm).counters cs 12=extractionSizeContribution tm (cs 2) (cs 1) := by
  change injectedTemplateCounters extractionSizeToTermRegister _ _ (extractionSizeToTermRegister 4)=_
  rw [injectedTemplateCounters_pull _ extractionSizeToTermRegister_injective,extractionSizeStepTemplate_counters]
  simp [extractionSizeToTermRegister,cleanupProgramTemplate,cleanupCounters_apply]

theorem extractionTermSizeProgramTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionTermSizeProgramTemplate tm).bytes cs=[] := by
  simp [extractionTermSizeProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate,injectProgramTemplate,
    extractionSizeStepTemplate_bytes]

end ShiReversibleGenerator
