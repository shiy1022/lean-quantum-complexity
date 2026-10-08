import ReversibleExtractionForwardPrefixTraversalCount
import ReversibleExtractionForwardPrefixTraversalMetadata
import ReversibleExtractionNaturalTermRangeSnoc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula

/-- Exact count of the original prefix compiler, accumulated by the actual descending loop. -/
theorem extractionForwardPrefixLoop_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (k : Nat) (cs : ExtractionTraversalRegister → Nat)
    (hk : k ≤ cs 0+1) (hell : cs 2=k-1) :
    descendingTemplateCounters (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k cs 16=
      cs 16+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 k).map
        (fun p => formulaElementaryLayers p+2)).sum := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateCounters,extractionNaturalTermRange]
  | succ k ih =>
    let next := Function.update cs (22 : ExtractionTraversalRegister) k
    let after := (extractionForwardPrefixTraversalStepTemplate tm e stride).counters next
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=k := by simpa [next] using hell
    have hn16 : next 16=cs 16 := by simp [next]
    have hm := extractionForwardPrefixTraversalStepTemplate_metadata tm e stride next
    dsimp only at hm
    rw [hn0,hn1,hn2] at hm
    have ha0 : after 0=cs 0 := hm.1
    have ha1 : after 1=cs 1 := hm.2.1
    have ha2 : after 2=k-1 := hm.2.2.2.1
    have hi := ih after (by rw [ha0]; omega) ha2
    rw [ha0,ha1] at hi
    have hc := extractionForwardPrefixTraversalStepTemplate_count tm e stride next (by rw [hn2,hn0]; omega)
    rw [hn0,hn1,hn2,hn16] at hc
    rw [descendingTemplateCounters]
    change descendingTemplateCounters (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k after 16=_
    rw [hi]
    change (extractionForwardPrefixTraversalStepTemplate tm e stride).counters next 16+_= _
    rw [hc,extractionNaturalTermRange_snoc]
    simp only [Nat.zero_add,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    omega

end ShiReversibleGenerator
