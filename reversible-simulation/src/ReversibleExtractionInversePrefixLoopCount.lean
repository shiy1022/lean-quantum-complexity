import ReversibleExtractionInversePrefixStepCount
import ReversibleExtractionNaturalTermRange
import ReversibleExtractionInversePrefixTraversalMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula

/-- The ambient step counts the original natural-coordinate term and its negation. -/
theorem extractionInversePrefixTraversalStepTemplate_count (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat)
    (hell : cs 2 ≤ cs 0) :
    (extractionInversePrefixTraversalStepTemplate tm e stride).counters cs 16=
      cs 16+formulaElementaryLayers (extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1))+2 := by
  have h := extractionTraversalLift_pull (extractionInversePrefixStepTemplate tm e stride) cs 16
  rw [extractionInversePrefixStepTemplate_count tm e stride _ hell] at h
  have h0 : extractionTermToTraversalRegister (0 : ExtractionTermRegister)=(0 : ExtractionTraversalRegister) := by decide
  have h1 : extractionTermToTraversalRegister (1 : ExtractionTermRegister)=(1 : ExtractionTraversalRegister) := by decide
  have h2 : extractionTermToTraversalRegister (2 : ExtractionTermRegister)=(2 : ExtractionTraversalRegister) := by decide
  have h16 : extractionTermToTraversalRegister (16 : ExtractionTermRegister)=(16 : ExtractionTraversalRegister) := by decide
  rw [h0,h1,h2,h16] at h
  simpa only [extractionNaturalTerm,formulaElementaryLayers_rename,extractionInversePrefixTraversalStepTemplate] using h


/-- The entire inverse-prefix loop counts exactly the original ascending term range. -/
theorem extractionInversePrefixLoop_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (k : Nat) (cs : ExtractionTraversalRegister → Nat) (hlimit : cs 2+k ≤ cs 0+1) :
    descendingTemplateCounters (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k cs 16=
      cs 16+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) k).map
        (fun p => formulaElementaryLayers p+2)).sum := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateCounters,extractionNaturalTermRange]
  | succ k ih =>
    let next := Function.update cs (22 : ExtractionTraversalRegister) k
    let after := (extractionInversePrefixTraversalStepTemplate tm e stride).counters next
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=cs 2 := by simp [next]
    have hn16 : next 16=cs 16 := by simp [next]
    have hm := extractionInversePrefixTraversalStepTemplate_metadata tm e stride next
    dsimp only at hm
    rw [hn0,hn1,hn2] at hm
    have h0 : after 0=cs 0 := hm.1
    have h1 : after 1=cs 1 := hm.2.1
    have h2 : after 2=cs 2+1 := hm.2.2.2.1
    have hc := extractionInversePrefixTraversalStepTemplate_count tm e stride next (by rw [hn2,hn0]; omega)
    rw [hn0,hn1,hn2,hn16] at hc
    change after 16=cs 16+formulaElementaryLayers (extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1))+2 at hc
    have hi := ih after (by rw [h2,h0]; omega)
    rw [h0,h1,h2] at hi
    rw [descendingTemplateCounters]
    change descendingTemplateCounters (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k after 16=_
    rw [hi,hc]
    simp only [extractionNaturalTermRange,List.map_cons,List.sum_cons,Nat.add_assoc]

end ShiReversibleGenerator
