import ReversibleExtractionForwardPrefixStep
import ReversibleExtractionForwardTermRetreatCounters
import ReversibleExtractionTermNegationFrames
import ReversibleExtractionBoundTermFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionForwardTermRetreatTemplate_scratch (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionForwardTermRetreatTemplate tm).counters cs 5=0 ∧
    (extractionForwardTermRetreatTemplate tm).counters cs 6=0 ∧
    (extractionForwardTermRetreatTemplate tm).counters cs 7=0 ∧
    (extractionForwardTermRetreatTemplate tm).counters cs 17=cs 17 := by
  simp [extractionForwardTermRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

/-- Each real prefix body starts by cleaning the scratch it subsequently needs. -/
theorem extractionForwardPrefixStepTemplate_ready (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) (h17 : cs 17=0) :
    (extractionForwardPrefixStepTemplate tm e stride).ready cs := by
  let after := (extractionForwardTermRetreatTemplate tm).counters cs
  have hs := extractionForwardTermRetreatTemplate_scratch tm cs
  have hf : ∀ q ∈ ([5,6,17] : List ExtractionTermRegister),
      (extractionTermNegationPrinterTemplate false).counters after q=after q := by
    intro q hq
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame false after _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨extractionForwardTermRetreatTemplate_ready tm cs,?_,?_,trivial⟩
  · exact extractionTermNegationPrinterTemplate_ready false after hs.2.2.1 (hs.2.2.2.trans h17)
  · exact extractionBoundTermPrinterTemplate_ready tm e stride false _
      ((hf 5 (by simp)).trans hs.1) ((hf 6 (by simp)).trans hs.2.1)
      ((hf 17 (by simp)).trans (hs.2.2.2.trans h17))

end ShiReversibleGenerator
