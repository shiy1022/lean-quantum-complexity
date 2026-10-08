import ReversibleExtractionForwardPrefixLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionForwardPrefixTraversalStepTemplate_buffer (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) :
    (extractionForwardPrefixTraversalStepTemplate tm e stride).counters cs 17=cs 17 := by
  have h := extractionTraversalLift_pull (extractionForwardPrefixStepTemplate tm e stride) cs 17
  rw [extractionForwardPrefixStepTemplate_frame _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at h
  exact h

/-- The actual prefix loop owns a disjoint counter, so source-index setup cannot corrupt its continuation. -/
theorem extractionForwardPrefixLoopTemplate_ready (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (h17 : cs 17=0) :
    (extractionForwardPrefixLoopTemplate tm e stride).ready cs := by
  suffices h : ∀ k (t : ExtractionTraversalRegister → Nat),t 17=0 →
      descendingTemplateReady (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k t by
    exact h _ _ h17
  intro k
  induction k with
  | zero => intro t ht; trivial
  | succ k ih =>
    intro t ht
    let next := Function.update t (22 : ExtractionTraversalRegister) k
    have hn : next 17=0 := by simpa [next] using ht
    refine ⟨?_,?_,ih _ ?_⟩
    · exact extractionForwardPrefixStepTemplate_ready tm e stride
        (fun r => next (extractionTermToTraversalRegister r)) hn
    · exact (extractionTraversalLift_outside (extractionForwardPrefixStepTemplate tm e stride)
        next 22 (by decide)).trans (Function.update_self _ _ _)
    · exact (extractionForwardPrefixTraversalStepTemplate_buffer tm e stride next).trans hn

end ShiReversibleGenerator
