import ReversibleExtractionPaddedLeaf
import ReversibleExtractionForwardPassSourceFrames
import ReversibleExtractionInversePassSourceFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionPaddedPassTemplate_source_frame (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (q : ExtractionTermRegister) (hq : q ∈ ([0,1,11] : List ExtractionTermRegister)) :
    (extractionPaddedPassTemplate tm e stride backward).counters cs
      (extractionTraversalToPaddedRegister (extractionTermToTraversalRegister q))=
      cs (extractionTraversalToPaddedRegister (extractionTermToTraversalRegister q)) := by
  cases backward
  · have h := extractionPaddedLift_pull (extractionForwardPassTemplate tm e stride) cs (extractionTermToTraversalRegister q)
    rw [extractionForwardPassTemplate_source_frame tm e stride _ q hq] at h
    exact h
  · have h := extractionPaddedLift_pull (extractionInversePassTemplate tm e stride) cs (extractionTermToTraversalRegister q)
    rw [extractionInversePassTemplate_source_frame tm e stride _ q hq] at h
    exact h

theorem extractionPaddedLeafTemplate_source_frame (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (q : ExtractionPaddedRegister) (hq : q ∈ ([0,1,11] : List ExtractionPaddedRegister)) :
    (extractionPaddedLeafTemplate tm e stride backward).counters cs q=cs q := by
  have hp : ∀ t : ExtractionPaddedRegister → Nat,
      (extractionPaddedPassTemplate tm e stride backward).counters t q=t q := by
    intro t
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact extractionPaddedPassTemplate_source_frame tm e stride backward t 0 (by simp)
    · exact extractionPaddedPassTemplate_source_frame tm e stride backward t 1 (by simp)
    · exact extractionPaddedPassTemplate_source_frame tm e stride backward t 11 (by simp)
  have hq16 : q ≠ 16 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  have hc : ∀ t : ExtractionPaddedRegister → Nat,extractionPaddedRootCopyTemplate.counters t q=t q := by
    intro t
    exact Function.update_of_ne hq16 _ _
  cases backward
  · exact (hp (extractionPaddedRootCopyTemplate.counters cs)).trans (hc cs)
  · exact (hc ((extractionPaddedPassTemplate tm e stride true).counters cs)).trans (hp cs)

end ShiReversibleGenerator
