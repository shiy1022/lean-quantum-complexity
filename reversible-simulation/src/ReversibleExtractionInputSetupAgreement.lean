import ReversibleExtractionInputSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Exact original configuration addresses follow from the actual index computation and binding run. -/
theorem extractionInputSetupTemplate_inputs (tm : Turing.FinTM2) (stride : Nat)
    (cs : ExtractionTermRegister → Nat) :
    let after := (extractionInputSetupTemplate tm stride).counters cs
    ∀ i,(extractionBoundInputs tm stride i).eval (Function.update after 3 (2*after 2))=
      cs 11+stride*naturalConfigurationAddress tm (cs 0) (extractionTermNaturalInput tm (cs 2) (cs 1) i) := by
  let indexed := (cleanupProgramTemplate [8]).counters
    (extractionIndexSetupTemplate.counters ((cleanupProgramTemplate [7,8]).counters cs))
  have hp : indexed 10= indexed 2-1 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have hv : indexed 4=indexed 1-indexed 2-1 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h := extractionInputBindingTemplate_inputs tm stride indexed hp hv
  have h0 : indexed 0=cs 0 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h1 : indexed 1=cs 1 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h2 : indexed 2=cs 2 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h11 : indexed 11=cs 11 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  simpa only [extractionInputSetupTemplate,sequenceProgramTemplate,indexed,h0,h1,h2,h11] using h

end ShiReversibleGenerator
