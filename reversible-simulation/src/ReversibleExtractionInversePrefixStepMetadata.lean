import ReversibleExtractionInversePrefixStepReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The actual ascending inverse body advances both runtime coordinates by the original term contribution. -/
theorem extractionInversePrefixStepTemplate_metadata (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionInversePrefixStepTemplate tm e stride).counters cs 2=cs 2+1 ∧
    (extractionInversePrefixStepTemplate tm e stride).counters cs 18=
      cs 18+(extractionSizeContribution tm (cs 2) (cs 1)-3) := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht2 : t 2=cs 2 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have ht18 : t 18=cs 18 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have ht12 : t 12=extractionSizeContribution tm (cs 2) (cs 1) := extractionTermSizeProgramTemplate_value tm cs
  have hu : ∀ q ∈ ([2,12,18] : List ExtractionTermRegister),u q=t q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionBoundTermPrinterTemplate_frame tm e stride true t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hv : ∀ q ∈ ([2,12,18] : List ExtractionTermRegister),v q=u q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame true u _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h2 := (hv 2 (by simp)).trans ((hu 2 (by simp)).trans ht2)
  have h18 := (hv 18 (by simp)).trans ((hu 18 (by simp)).trans ht18)
  have h12 := (hv 12 (by simp)).trans ((hu 12 (by simp)).trans ht12)
  change extractionPrefixAdvanceTemplate.counters v 2=cs 2+1 ∧
    extractionPrefixAdvanceTemplate.counters v 18=cs 18+(extractionSizeContribution tm (cs 2) (cs 1)-3)
  simp [extractionPrefixAdvanceTemplate_counters,h2,h18,h12]

end ShiReversibleGenerator
