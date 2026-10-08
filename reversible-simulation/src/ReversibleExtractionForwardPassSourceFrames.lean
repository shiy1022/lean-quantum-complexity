import ReversibleExtractionForwardPass
import ReversibleExtractionForwardPrefixTraversalMetadata
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionForwardPrefixLoopTemplate_source_frame (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat)
    (q : ExtractionTermRegister) (hq : q ∈ ([0,1,11] : List ExtractionTermRegister)) :
    (extractionForwardPrefixLoopTemplate tm e stride).counters cs (extractionTermToTraversalRegister q)=
      cs (extractionTermToTraversalRegister q) := by
  apply descendingProgramTemplate_point_frame
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  · intro t
    have hm := extractionForwardPrefixTraversalStepTemplate_metadata tm e stride t
    dsimp only at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hm.1
    · exact hm.2.1
    · exact hm.2.2.1

theorem extractionForwardPassTemplate_source_frame (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat)
    (q : ExtractionTermRegister) (hq : q ∈ ([0,1,11] : List ExtractionTermRegister)) :
    (extractionForwardPassTemplate tm e stride).counters cs (extractionTermToTraversalRegister q)=
      cs (extractionTermToTraversalRegister q) := by
  let t := (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).counters cs
  let u := extractionDescendingPassHandoffTemplate.counters t
  have ht : t (extractionTermToTraversalRegister q)=cs (extractionTermToTraversalRegister q) :=
    extractionForwardClosingLift_source_frame tm cs q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  have hu : u (extractionTermToTraversalRegister q)=t (extractionTermToTraversalRegister q) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals simp [u,extractionDescendingPassHandoffTemplate_counters,extractionTermToTraversalRegister,cleanupCounters_apply]
  exact (extractionForwardPrefixLoopTemplate_source_frame tm e stride u q hq).trans (hu.trans ht)

end ShiReversibleGenerator
