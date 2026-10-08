import ReversibleExtractionInversePass
import ReversibleExtractionInversePrefixSourceFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInverseClosingLoopTemplate_source_frame (tm : Turing.FinTM2)
    (cs : ExtractionTraversalRegister → Nat) (q : ExtractionTermRegister)
    (hq : q ∈ ([0,1,11,17] : List ExtractionTermRegister)) :
    (extractionInverseClosingLoopTemplate tm).counters cs (extractionTermToTraversalRegister q)=
      cs (extractionTermToTraversalRegister q) := by
  apply descendingProgramTemplate_point_frame
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide
  · intro t
    have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) t q
    rw [extractionInverseClosingStepTemplate_source_frame tm _ q hq] at h
    exact h

theorem extractionInversePassTemplate_source_frame (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat)
    (q : ExtractionTermRegister) (hq : q ∈ ([0,1,11] : List ExtractionTermRegister)) :
    (extractionInversePassTemplate tm e stride).counters cs (extractionTermToTraversalRegister q)=
      cs (extractionTermToTraversalRegister q) := by
  let t := (extractionInversePrefixLoopTemplate tm e stride).counters cs
  let u := extractionInverseClosingHandoffTemplate.counters t
  have ht : t (extractionTermToTraversalRegister q)=cs (extractionTermToTraversalRegister q) :=
    extractionInversePrefixLoopTemplate_source_frame tm e stride cs q hq
  have hu : u (extractionTermToTraversalRegister q)=t (extractionTermToTraversalRegister q) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals simp [u,extractionInverseClosingHandoffTemplate_counters,extractionTermToTraversalRegister,cleanupCounters_apply]
  exact (extractionInverseClosingLoopTemplate_source_frame tm u q (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)).trans (hu.trans ht)

end ShiReversibleGenerator
