import ReversibleExtractionBoundTermScratchMetadata
import ReversibleExtractionForwardPrefixStepMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Full prefix execution retains exact bounded scratch/cache values from the real setup. -/
theorem extractionForwardPrefixStepTemplate_scratch (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 3=2*cs 2 ∧
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 4=cs 1-cs 2-1 ∧
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 7=0 ∧
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 8=0 ∧
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 9=0 ∧
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 10=cs 2-1 := by
  let t := (extractionForwardTermRetreatTemplate tm).counters cs
  let u := (extractionTermNegationPrinterTemplate false).counters t
  have ht : ∀ q ∈ ([1,2] : List ExtractionTermRegister),t q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    all_goals exact (extractionForwardTermRetreatTemplate_frame tm cs _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hu : ∀ q ∈ ([1,2] : List ExtractionTermRegister),u q=t q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame false t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h1 := (hu 1 (by simp)).trans (ht 1 (by simp))
  have h2 := (hu 2 (by simp)).trans (ht 2 (by simp))
  have hx := extractionBoundTermPrinterTemplate_scratch tm e stride false u
  simpa only [extractionForwardPrefixStepTemplate,sequenceProgramTemplate,decrementProgramTemplate,
    Function.update_of_ne (by decide : (3 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (4 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (7 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (8 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (9 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (10 : ExtractionTermRegister) ≠ 2),h1,h2] using hx

/-- Size and guard scratch remain exactly the checked retreat computation's values. -/
theorem extractionForwardPrefixStepTemplate_size_scratch (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 5=0 ∧
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 6=0 ∧
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 12=extractionSizeContribution tm (cs 2) (cs 1) := by
  have hf : ∀ q ∈ ([5,6,12] : List ExtractionTermRegister),
      (extractionForwardPrefixStepTemplate tm e stride).counters cs q=
        (extractionForwardTermRetreatTemplate tm).counters cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionForwardPrefixStepTemplate_retreat_frame tm e stride cs _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  simp [hf 5 (by simp),hf 6 (by simp),hf 12 (by simp),extractionForwardTermRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

end ShiReversibleGenerator
