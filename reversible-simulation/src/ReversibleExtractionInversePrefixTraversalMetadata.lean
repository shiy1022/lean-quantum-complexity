import ReversibleExtractionInversePrefixStepMetadata
import ReversibleExtractionInversePrefixLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInversePrefixStepTemplate_source_frame (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat)
    (q : ExtractionTermRegister) (hq : q ∈ ([0,1,11] : List ExtractionTermRegister)) :
    (extractionInversePrefixStepTemplate tm e stride).counters cs q=cs q := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht : t q=cs q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have hu : u q=t q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionBoundTermPrinterTemplate_frame tm e stride true t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hv : v q=u q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame true u _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have he : extractionPrefixAdvanceTemplate.counters v q=v q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals simp [extractionPrefixAdvanceTemplate_counters]
  exact he.trans (hv.trans (hu.trans ht))

/-- Ambient inverse traversal preserves input sources, advances length and advances the base exactly. -/
theorem extractionInversePrefixTraversalStepTemplate_metadata (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) :
    let after := (extractionInversePrefixTraversalStepTemplate tm e stride).counters cs
    after 0=cs 0 ∧ after 1=cs 1 ∧ after 11=cs 11 ∧ after 2=cs 2+1 ∧
      after 18=cs 18+(extractionSizeContribution tm (cs 2) (cs 1)-3) := by
  have hf : ∀ q ∈ ([0,1,11] : List ExtractionTermRegister),
      (extractionInversePrefixTraversalStepTemplate tm e stride).counters cs (extractionTermToTraversalRegister q)=
        cs (extractionTermToTraversalRegister q) := by
    intro q hq
    have h := extractionTraversalLift_pull (extractionInversePrefixStepTemplate tm e stride) cs q
    rw [extractionInversePrefixStepTemplate_source_frame tm e stride _ q hq] at h
    exact h
  refine ⟨hf 0 (by simp),hf 1 (by simp),hf 11 (by simp),?_,?_⟩
  · have h := extractionTraversalLift_pull (extractionInversePrefixStepTemplate tm e stride) cs 2
    rw [(extractionInversePrefixStepTemplate_metadata tm e stride _).1] at h
    exact h
  · have h := extractionTraversalLift_pull (extractionInversePrefixStepTemplate tm e stride) cs 18
    rw [(extractionInversePrefixStepTemplate_metadata tm e stride _).2] at h
    exact h

end ShiReversibleGenerator
