import ReversibleExtractionInversePrefixStep
import ReversibleExtractionBoundTermScratchMetadata
import ReversibleExtractionBoundTermFrames
import ReversibleExtractionTermNegationFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The ascending inverse prefix body cleans its own scratch and preserves the empty printer buffer. -/
theorem extractionInversePrefixStepTemplate_ready (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) (h17 : cs 17=0) :
    (extractionInversePrefixStepTemplate tm e stride).ready cs := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  have ht : t 5=0 ∧ t 6=0 ∧ t 7=0 ∧ t 17=0 := by
    simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply,h17]
  have hu7 : u 7=0 := (extractionBoundTermPrinterTemplate_scratch tm e stride true t).2.2.1
  have hu17 : u 17=0 := by
    exact (extractionBoundTermPrinterTemplate_frame tm e stride true t 17
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht.2.2.2
  refine ⟨extractionTermSizeProgramTemplate_ready tm cs,
    extractionBoundTermPrinterTemplate_ready tm e stride true t ht.1 ht.2.1 ht.2.2.2,
    extractionTermNegationPrinterTemplate_ready true u hu7 hu17,?_⟩
  apply extractionPrefixAdvanceTemplate_ready
  exact (extractionTermNegationPrinterTemplate_frame true u 7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu7

end ShiReversibleGenerator
