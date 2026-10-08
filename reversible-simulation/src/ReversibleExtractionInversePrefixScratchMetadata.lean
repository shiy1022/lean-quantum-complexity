import ReversibleExtractionInversePrefixStepReady
import ReversibleExtractionBoundTermScratchMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Exact overwritten cache and index values at the end of the real inverse body. -/
theorem extractionInversePrefixStepTemplate_scratch (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    let after := (extractionInversePrefixStepTemplate tm e stride).counters cs
    after 3=2*cs 2 ∧ after 4=cs 1-cs 2-1 ∧ after 7=0 ∧ after 9=0 ∧ after 10=cs 2-1 := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht1 : t 1=cs 1 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have ht2 : t 2=cs 2 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have hx := extractionBoundTermPrinterTemplate_scratch tm e stride true t
  change u 3=2*t 2 ∧ u 4=t 1-t 2-1 ∧ u 7=0 ∧ u 8=0 ∧ u 9=0 ∧ u 10=t 2-1 at hx
  rw [ht1,ht2] at hx
  have hf : ∀ q ∈ ([3,4,7,9,10] : List ExtractionTermRegister),
      (extractionInversePrefixStepTemplate tm e stride).counters cs q=u q := by
    intro q hq
    have hn : q ≠ 2 ∧ q ≠ 18 ∧ q ≠ 8 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    change extractionPrefixAdvanceTemplate.counters v q=u q
    rw [extractionPrefixAdvanceTemplate_counters,Function.update_of_ne hn.1,
      Function.update_of_ne hn.2.1,Function.update_of_ne hn.2.2]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame true u _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  simpa only [hf 3 (by simp),hf 4 (by simp),hf 7 (by simp),hf 9 (by simp),hf 10 (by simp)] using
    And.intro hx.1 (And.intro hx.2.1 (And.intro hx.2.2.1 (And.intro hx.2.2.2.2.1 hx.2.2.2.2.2)))

/-- Guard scratch stays cleared and the copied advance amount is exactly size-plus-four minus three. -/
theorem extractionInversePrefixStepTemplate_size_scratch (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    let after := (extractionInversePrefixStepTemplate tm e stride).counters cs
    after 5=0 ∧ after 6=0 ∧ after 12=extractionSizeContribution tm (cs 2) (cs 1) ∧
      after 8=extractionSizeContribution tm (cs 2) (cs 1)-3 := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have hu : ∀ q ∈ ([5,6,12] : List ExtractionTermRegister),u q=t q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionBoundTermPrinterTemplate_frame tm e stride true t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hv : ∀ q ∈ ([5,6,12] : List ExtractionTermRegister),v q=u q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame true u _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h5 : v 5=0 := by rw [hv 5 (by simp),hu 5 (by simp)]; simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have h6 : v 6=0 := by rw [hv 6 (by simp),hu 6 (by simp)]; simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have h12 : v 12=extractionSizeContribution tm (cs 2) (cs 1) := by
    rw [hv 12 (by simp),hu 12 (by simp)]
    exact extractionTermSizeProgramTemplate_value tm cs
  change extractionPrefixAdvanceTemplate.counters v 5=0 ∧ extractionPrefixAdvanceTemplate.counters v 6=0 ∧
    extractionPrefixAdvanceTemplate.counters v 12=_ ∧ extractionPrefixAdvanceTemplate.counters v 8=_
  simp [extractionPrefixAdvanceTemplate_counters,h5,h6,h12]

end ShiReversibleGenerator
