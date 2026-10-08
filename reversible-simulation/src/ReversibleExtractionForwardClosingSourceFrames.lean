import ReversibleExtractionForwardClosingLoop
import ReversibleExtractionClosingStepFrames
import ReversibleDescendingTemplatePointFrames
import ReversibleExtractionTraversalRegisterInjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionForwardClosingLoopTemplate_source_frame (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (hq : q ∈ ([0,1,11,17] : List ExtractionTermRegister)) :
    (extractionForwardClosingLoopTemplate tm).counters cs q=cs q := by
  apply descendingProgramTemplate_point_frame
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide
  · intro t
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact (extractionClosingStepTemplate_frame tm false t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

theorem extractionForwardClosingLift_source_frame (tm : Turing.FinTM2)
    (cs : ExtractionTraversalRegister → Nat) (q : ExtractionTermRegister)
    (hq : q ∈ ([0,1,11,17] : List ExtractionTermRegister)) :
    (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).counters cs
      (extractionTermToTraversalRegister q)=cs (extractionTermToTraversalRegister q) := by
  rw [extractionTraversalLift_pull,extractionForwardClosingLoopTemplate_source_frame tm _ q hq]

end ShiReversibleGenerator
