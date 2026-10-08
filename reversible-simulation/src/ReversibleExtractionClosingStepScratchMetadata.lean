import ReversibleExtractionClosingStepMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionBoundClosingPrinterTemplate_cache (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 3=2*cs 2 ∧
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 5=0 ∧
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 6=0 ∧
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 7=0 ∧
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 12=extractionSizeContribution tm (cs 2) (cs 1) := by
  have hf : ∀ q ∈ ([3,5,6,7,12] : List ExtractionTermRegister),
      (extractionBoundClosingPrinterTemplate tm backward).counters cs q=
        (extractionClosingSetupTemplate tm).counters cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals exact (fixedNodeCounters_other extractionTermNodeRegisters _ _ (by decide) (by decide) (by decide) (by decide) _)
  simp [hf 3 (by simp),hf 5 (by simp),hf 6 (by simp),hf 7 (by simp),hf 12 (by simp),
    extractionClosingSetupTemplate_counters,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

theorem extractionClosingStepTemplate_cache (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionClosingStepTemplate tm backward).counters cs 3=2*cs 2 ∧
    (extractionClosingStepTemplate tm backward).counters cs 5=0 ∧
    (extractionClosingStepTemplate tm backward).counters cs 6=0 ∧
    (extractionClosingStepTemplate tm backward).counters cs 7=0 ∧
    (extractionClosingStepTemplate tm backward).counters cs 12=extractionSizeContribution tm (cs 2) (cs 1) := by
  simpa [extractionClosingStepTemplate,sequenceProgramTemplate,extractionClosingAdvanceTemplate_counters] using
    extractionBoundClosingPrinterTemplate_cache tm backward cs

end ShiReversibleGenerator
