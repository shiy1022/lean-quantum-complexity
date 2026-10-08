import ReversibleExtractionForwardPrefixStepFrames
import ReversibleDescendingProgramTemplate

set_option autoImplicit false
namespace ShiReversibleGenerator

noncomputable def extractionForwardPrefixLoopTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  descendingProgramTemplate (extractionForwardPrefixTraversalStepTemplate tm e stride)
    (22 : ExtractionTraversalRegister)

theorem extractionForwardPrefixLoopTemplate_embeds (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionForwardPrefixLoopTemplate tm e stride).Embeds :=
  descendingProgramTemplate_embeds _ _ (extractionTraversalLift_embeds _)

theorem extractionForwardPrefixLoopTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionForwardPrefixLoopTemplate tm e stride).Runs :=
  descendingProgramTemplate_run _ _ (extractionTraversalLift_embeds _)
    (extractionForwardPrefixTraversalStepTemplate_run tm e stride)

end ShiReversibleGenerator
