import ReversibleExtractionForwardPrefixStepCount
import ReversibleExtractionNaturalTermRange
import ReversibleExtractionForwardPrefixLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula

/-- The ambient step counts the original natural-coordinate term and its negation. -/
theorem extractionForwardPrefixTraversalStepTemplate_count (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat)
    (hell : cs 2 ≤ cs 0) :
    (extractionForwardPrefixTraversalStepTemplate tm e stride).counters cs 16=
      cs 16+formulaElementaryLayers (extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1))+2 := by
  have h := extractionTraversalLift_pull (extractionForwardPrefixStepTemplate tm e stride) cs 16
  rw [extractionForwardPrefixStepTemplate_count tm e stride _ hell] at h
  have h0 : extractionTermToTraversalRegister (0 : ExtractionTermRegister)=(0 : ExtractionTraversalRegister) := by decide
  have h1 : extractionTermToTraversalRegister (1 : ExtractionTermRegister)=(1 : ExtractionTraversalRegister) := by decide
  have h2 : extractionTermToTraversalRegister (2 : ExtractionTermRegister)=(2 : ExtractionTraversalRegister) := by decide
  have h16 : extractionTermToTraversalRegister (16 : ExtractionTermRegister)=(16 : ExtractionTraversalRegister) := by decide
  rw [h0,h1,h2,h16] at h
  simpa only [extractionNaturalTerm,formulaElementaryLayers_rename,extractionForwardPrefixTraversalStepTemplate] using h

end ShiReversibleGenerator
