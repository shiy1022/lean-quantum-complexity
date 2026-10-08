import ReversibleExtractionInverseClosingStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInverseClosingStepTemplate_source_frame (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (hq : q ∈ ([0,1,11,17] : List ExtractionTermRegister)) :
    (extractionInverseClosingStepTemplate tm).counters cs q=cs q := by
  let t := (extractionInverseClosingRetreatTemplate tm).counters cs
  let u := (extractionBoundClosingPrinterTemplate tm true).counters t
  have ht : t q=cs q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact (extractionInverseClosingRetreatTemplate_frame tm cs _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hu : u q=t q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact (extractionBoundClosingPrinterTemplate_frame tm true t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
  have he : extractionInverseClosingAdvanceTemplate.counters u q=u q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals simp [extractionInverseClosingAdvanceTemplate_counters]
  exact he.trans (hu.trans ht)

/-- The closing endpoint increases by three while the selected term and term base retreat. -/
theorem extractionInverseClosingStepTemplate_metadata (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    let after := (extractionInverseClosingStepTemplate tm).counters cs
    after 2=cs 2-1 ∧ after 18=cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) ∧
      after 20=cs 20+3 := by
  let t := (extractionInverseClosingRetreatTemplate tm).counters cs
  let u := (extractionBoundClosingPrinterTemplate tm true).counters t
  have ht2 : t 2=cs 2 := extractionInverseClosingRetreatTemplate_frame tm cs 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have ht20 : t 20=cs 20 := extractionInverseClosingRetreatTemplate_frame tm cs 20
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have ht18 : t 18=cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) :=
    extractionInverseClosingRetreatTemplate_base tm cs
  have hu : ∀ q ∈ ([2,18,20] : List ExtractionTermRegister),u q=t q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionBoundClosingPrinterTemplate_frame tm true t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
  change extractionInverseClosingAdvanceTemplate.counters u 2=_ ∧
    extractionInverseClosingAdvanceTemplate.counters u 18=_ ∧ extractionInverseClosingAdvanceTemplate.counters u 20=_
  simp [extractionInverseClosingAdvanceTemplate_counters,hu 2 (by simp),hu 18 (by simp),hu 20 (by simp),ht2,ht18,ht20]

theorem extractionInverseClosingStepTemplate_count (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingStepTemplate tm).counters cs 16=cs 16+41 := by
  let t := (extractionInverseClosingRetreatTemplate tm).counters cs
  have ht : t 16=cs 16 := extractionInverseClosingRetreatTemplate_frame tm cs 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change extractionInverseClosingAdvanceTemplate.counters
    ((extractionBoundClosingPrinterTemplate tm true).counters t) 16=_
  simp [extractionInverseClosingAdvanceTemplate_counters,extractionBoundClosingPrinterTemplate_count,ht]

end ShiReversibleGenerator
