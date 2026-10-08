import ReversibleExtractionInverseClosingLoop
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInverseClosingTraversalStepTemplate_count (tm : Turing.FinTM2)
    (cs : ExtractionTraversalRegister → Nat) :
    (extractionInverseClosingTraversalStepTemplate tm).counters cs 16=cs 16+41 := by
  have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) cs 16
  rw [extractionInverseClosingStepTemplate_count] at h
  exact h

theorem extractionInverseClosingLoopTemplate_count (tm : Turing.FinTM2)
    (cs : ExtractionTraversalRegister → Nat) :
    (extractionInverseClosingLoopTemplate tm).counters cs 16=cs 16+41*cs 22 := by
  have h : ∀ k (t : ExtractionTraversalRegister → Nat),
      descendingTemplateCounters (extractionInverseClosingTraversalStepTemplate tm) 22 k t 16=t 16+41*k := by
    intro k
    induction k with
    | zero => intro t; simp [descendingTemplateCounters]
    | succ k ih =>
      intro t
      rw [descendingTemplateCounters,ih,extractionInverseClosingTraversalStepTemplate_count]
      simp only [Nat.mul_succ,Function.update_of_ne (by decide : (16 : ExtractionTraversalRegister) ≠ 22)]
      omega
  change Function.update (descendingTemplateCounters _ 22 (cs 22) cs) 22 0 16=_
  rw [Function.update_of_ne (by decide : (16 : ExtractionTraversalRegister) ≠ 22),h]

theorem extractionInverseClosingLoopTemplate_remaining (tm : Turing.FinTM2)
    (cs : ExtractionTraversalRegister → Nat) :
    (extractionInverseClosingLoopTemplate tm).counters cs 22=0 := by
  simp [extractionInverseClosingLoopTemplate,descendingProgramTemplate]

theorem extractionInverseClosingLoopTemplate_buffer (tm : Turing.FinTM2)
    (cs : ExtractionTraversalRegister → Nat) :
    (extractionInverseClosingLoopTemplate tm).counters cs 17=cs 17 :=
  descendingProgramTemplate_point_frame (extractionInverseClosingTraversalStepTemplate tm) 22 17
    (by decide) (extractionInverseClosingTraversalStepTemplate_buffer tm) cs

end ShiReversibleGenerator
