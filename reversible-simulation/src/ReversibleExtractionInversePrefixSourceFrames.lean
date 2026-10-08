import ReversibleExtractionInversePrefixTraversalMetadata
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInversePrefixLoopTemplate_source_frame (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat)
    (q : ExtractionTermRegister) (hq : q ∈ ([0,1,11] : List ExtractionTermRegister)) :
    (extractionInversePrefixLoopTemplate tm e stride).counters cs (extractionTermToTraversalRegister q)=
      cs (extractionTermToTraversalRegister q) := by
  apply descendingProgramTemplate_point_frame
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro t
    have h := extractionTraversalLift_pull (extractionInversePrefixStepTemplate tm e stride) t q
    rw [extractionInversePrefixStepTemplate_source_frame tm e stride _ q hq] at h
    exact h

end ShiReversibleGenerator
