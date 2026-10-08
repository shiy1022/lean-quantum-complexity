import ReversibleExtractionClosingStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionBoundClosingPrinterTemplate_termSize (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 12=extractionSizeContribution tm (cs 2) (cs 1) := by
  change fixedNodeCounters extractionTermNodeRegisters _ ((extractionClosingSetupTemplate tm).counters cs) 12=_
  rw [fixedNodeCounters_other _ _ 12 (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])]
  rw [extractionClosingSetupTemplate_counters]
  simpa only [Function.update_of_ne (by decide : (12 : ExtractionTermRegister) ≠ 21),
    Function.update_of_ne (by decide : (12 : ExtractionTermRegister) ≠ 19)] using
      extractionTermSizeProgramTemplate_value tm cs

theorem extractionClosingStepTemplate_metadata (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionClosingStepTemplate tm backward).counters cs 2=cs 2+1 ∧
    (extractionClosingStepTemplate tm backward).counters cs 18=cs 18+extractionSizeContribution tm (cs 2) (cs 1)-3 ∧
    (extractionClosingStepTemplate tm backward).counters cs 20=cs 20-3 := by
  have frame : ∀ q ∈ ([2,18,20] : List ExtractionTermRegister),
      (extractionBoundClosingPrinterTemplate tm backward).counters cs q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq | hq | hq
    all_goals subst q
    all_goals exact extractionBoundClosingPrinterTemplate_frame tm backward cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [extractionClosingStepTemplate,sequenceProgramTemplate,extractionClosingAdvanceTemplate_counters]
  simp [frame 2 (by simp),frame 18 (by simp),frame 20 (by simp),extractionBoundClosingPrinterTemplate_termSize]

theorem extractionClosingStepTemplate_termBase (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) :
    (extractionClosingStepTemplate tm backward).counters cs 18=cs 18+
      (Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))).size+1 := by
  rw [(extractionClosingStepTemplate_metadata tm backward cs).2.1,
    extractionSizeContribution_exact tm e (cs 0) (cs 2) (cs 1) hell]
  omega

end ShiReversibleGenerator
