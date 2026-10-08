import ReversibleExtractionWholeSizeProgram
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionSizeMasterTemplate_source_frame (tm : Turing.FinTM2)
    (cs : ExtractionSizeRegister → Nat) (q : ExtractionSizeRegister)
    (hq : q ∈ ([0,1,11] : List ExtractionSizeRegister)) :
    (extractionSizeMasterTemplate tm).counters cs q=cs q := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · have h := descendingProgramTemplate_point_frame (extractionSizeStepTemplate tm) 2 0 (by decide)
      (by intro t; rw [extractionSizeStepTemplate_counters]; simp) (extractionSizeSetupTemplate.counters cs)
    exact h.trans (by simp [extractionSizeSetupTemplate_counters,cleanupCounters_apply])
  · have h := descendingProgramTemplate_point_frame (extractionSizeStepTemplate tm) 2 1 (by decide)
      (by intro t; rw [extractionSizeStepTemplate_counters]; simp) (extractionSizeSetupTemplate.counters cs)
    exact h.trans (by simp [extractionSizeSetupTemplate_counters,cleanupCounters_apply])
  · have h := descendingProgramTemplate_point_frame (extractionSizeStepTemplate tm) 2 11 (by decide)
      (by intro t; rw [extractionSizeStepTemplate_counters]; simp) (extractionSizeSetupTemplate.counters cs)
    exact h.trans (by simp [extractionSizeSetupTemplate_counters,cleanupCounters_apply])

theorem extractionWholeSizeProgramTemplate_source_frame (tm : Turing.FinTM2)
    (cs : ExtractionPaddedRegister → Nat) (q : ExtractionPaddedRegister)
    (hq : q ∈ ([0,1,4,11,16,17,18,24,25] : List ExtractionPaddedRegister)) :
    (extractionWholeSizeProgramTemplate tm).counters cs q=cs q := by
  have hsmall : ∀ r ∈ ([0,1,11] : List ExtractionSizeRegister),
      (extractionWholeSizeProgramTemplate tm).counters cs (extractionSizeToPaddedRegister r)=
        cs (extractionSizeToPaddedRegister r) := by
    intro r hr
    have h := injectedTemplateCounters_pull extractionSizeToPaddedRegister extractionSizeToPaddedRegister_injective cs
      ((extractionSizeMasterTemplate tm).counters (fun z => cs (extractionSizeToPaddedRegister z))) r
    rw [extractionSizeMasterTemplate_source_frame tm _ r hr] at h
    exact h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsmall 0 (by simp)
  · exact hsmall 1 (by simp)
  · apply injectedTemplateCounters_outside
    intro r hr
    have hv := congrArg Fin.val hr
    simp only [extractionSizeToPaddedRegister,extractionTraversalToPaddedRegister,
      extractionTermToTraversalRegister,extractionSizeToTermRegister] at hv
    split_ifs at hv <;> omega
  · exact hsmall 11 (by simp)
  all_goals exact extractionWholeSizeProgramTemplate_outside tm cs _ (by decide)

end ShiReversibleGenerator
