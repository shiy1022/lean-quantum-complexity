import ReversibleExtractionForwardPrefixStepMetadata
import ReversibleExtractionForwardPrefixLoopReady

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The ambient runtime state retains its sources, descends in length and retreats the term base exactly. -/
theorem extractionForwardPrefixTraversalStepTemplate_metadata (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) :
    let after := (extractionForwardPrefixTraversalStepTemplate tm e stride).counters cs
    after 0=cs 0 ∧ after 1=cs 1 ∧ after 11=cs 11 ∧ after 2=cs 2-1 ∧
      after 18=cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) := by
  have hf : ∀ q ∈ ([0,1,11] : List ExtractionTermRegister),
      (extractionForwardPrefixTraversalStepTemplate tm e stride).counters cs (extractionTermToTraversalRegister q)=
        cs (extractionTermToTraversalRegister q) := by
    intro q hq
    have h := extractionTraversalLift_pull (extractionForwardPrefixStepTemplate tm e stride) cs q
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals rw [extractionForwardPrefixStepTemplate_frame _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at h
    all_goals exact h
  refine ⟨hf 0 (by simp),hf 1 (by simp),hf 11 (by simp),?_,?_⟩
  · have h := extractionTraversalLift_pull (extractionForwardPrefixStepTemplate tm e stride) cs 2
    rw [extractionForwardPrefixStepTemplate_length] at h
    exact h
  · have h := extractionTraversalLift_pull (extractionForwardPrefixStepTemplate tm e stride) cs 18
    rw [extractionForwardPrefixStepTemplate_base] at h
    exact h

end ShiReversibleGenerator
