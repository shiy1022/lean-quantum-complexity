import ReversibleExtractionInverseClosingStepMetadata
import ReversibleExtractionTraversalRegisterInjection
import ReversibleDescendingProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

noncomputable def extractionInverseClosingTraversalStepTemplate (tm : Turing.FinTM2)
     :=
  extractionTraversalLift (extractionInverseClosingStepTemplate tm)

/-- Ascending inverse traversal uses the disjoint outer counter22. -/
noncomputable def extractionInverseClosingLoopTemplate (tm : Turing.FinTM2)
     :=
  descendingProgramTemplate (extractionInverseClosingTraversalStepTemplate tm) 22

theorem extractionInverseClosingLoopTemplate_embeds (tm : Turing.FinTM2)
     :
    (extractionInverseClosingLoopTemplate tm).Embeds :=
  descendingProgramTemplate_embeds _ _ (extractionTraversalLift_embeds _)

theorem extractionInverseClosingLoopTemplate_run (tm : Turing.FinTM2)
     :
    (extractionInverseClosingLoopTemplate tm).Runs :=
  descendingProgramTemplate_run _ _ (extractionTraversalLift_embeds _)
    (extractionTraversalLift_run _ (extractionInverseClosingStepTemplate_embeds tm)
      (extractionInverseClosingStepTemplate_run tm))

theorem extractionInverseClosingTraversalStepTemplate_buffer (tm : Turing.FinTM2)
     (cs : ExtractionTraversalRegister → Nat) :
    (extractionInverseClosingTraversalStepTemplate tm).counters cs 17=cs 17 := by
  have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) cs 17
  rw [extractionInverseClosingStepTemplate_source_frame tm _ 17 (by simp)] at h
  exact h

theorem extractionInverseClosingLoopTemplate_ready (tm : Turing.FinTM2)
     (cs : ExtractionTraversalRegister → Nat) (h17 : cs 17=0) :
    (extractionInverseClosingLoopTemplate tm).ready cs := by
  suffices h : ∀ k (t : ExtractionTraversalRegister → Nat),t 17=0 →
      descendingTemplateReady (extractionInverseClosingTraversalStepTemplate tm) 22 k t by
    exact h _ _ h17
  intro k
  induction k with
  | zero => intro t ht; trivial
  | succ k ih =>
    intro t ht
    let next := Function.update t (22 : ExtractionTraversalRegister) k
    have hn : next 17=0 := by simpa [next] using ht
    refine ⟨?_,?_,ih _ ?_⟩
    · exact extractionInverseClosingStepTemplate_ready tm
        (fun r => next (extractionTermToTraversalRegister r)) hn
    · exact (extractionTraversalLift_outside (extractionInverseClosingStepTemplate tm)
        next 22 (by decide)).trans (Function.update_self _ _ _)
    · exact (extractionInverseClosingTraversalStepTemplate_buffer tm next).trans hn

end ShiReversibleGenerator
