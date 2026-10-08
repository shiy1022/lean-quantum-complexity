import ReversibleExtractionInversePrefixTraversalMetadata
import ReversibleExtractionInversePrefixNaturalPayload
import ReversibleExtractionDisjoinPasses

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Ascending runtime inverse printing prepends blocks in exactly the reverse original compiler order. -/
theorem extractionInversePrefixLoop_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (k : Nat) (cs : ExtractionTraversalRegister → Nat)
    (hlimit : cs 2+k ≤ cs 0+1) :
    descendingTemplateBytes (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k cs=
      (((disjoinTermPrefix (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit) (cs 18)
        (extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) k)).reverse).map
          (rawAssignmentPayload true)).flatten := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateBytes,extractionNaturalTermRange,disjoinTermPrefix]
  | succ k ih =>
    let next := Function.update cs (22 : ExtractionTraversalRegister) k
    let after := (extractionInversePrefixTraversalStepTemplate tm e stride).counters next
    let small : ExtractionTermRegister → Nat := fun r => next (extractionTermToTraversalRegister r)
    let p := extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1)
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=cs 2 := by simp [next]
    have hn11 : next 11=cs 11 := by simp [next]
    have hn18 : next 18=cs 18 := by simp [next]
    have hs0 : small 0=cs 0 := hn0
    have hs1 : small 1=cs 1 := hn1
    have hs2 : small 2=cs 2 := hn2
    have hs11 : small 11=cs 11 := hn11
    have hs18 : small 18=cs 18 := hn18
    have hm := extractionInversePrefixTraversalStepTemplate_metadata tm e stride next
    dsimp only at hm
    rw [hn0,hn1,hn2,hn11,hn18] at hm
    have ha0 : after 0=cs 0 := hm.1
    have ha1 : after 1=cs 1 := hm.2.1
    have ha11 : after 11=cs 11 := hm.2.2.1
    have ha2 : after 2=cs 2+1 := hm.2.2.2.1
    have hc : extractionSizeContribution tm (cs 2) (cs 1)=p.size+4 :=
      (extractionNaturalTerm_size tm e (cs 0) (cs 2) (cs 1) (by omega)).symm
    have ha18 : after 18=cs 18+p.size+1 := by
      have h := hm.2.2.2.2
      rw [hc] at h
      change after 18=cs 18+(p.size+4-3) at h
      omega
    have hi := ih after (by rw [ha2,ha0]; omega)
    rw [ha0,ha1,ha11,ha2,ha18] at hi
    have hp := extractionInversePrefixStepTemplate_natural_payload tm e stride small (by rw [hs2,hs0]; omega)
    dsimp only at hp
    rw [hs0,hs1,hs2,hs11,hs18] at hp
    rw [descendingTemplateBytes]
    change descendingTemplateBytes (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k after ++
      (extractionInversePrefixTraversalStepTemplate tm e stride).bytes next=_
    rw [hi]
    change _ ++ (extractionInversePrefixStepTemplate tm e stride).bytes small=_
    rw [hp]
    simp only [extractionNaturalTermRange,disjoinTermPrefix,List.reverse_append,List.map_append,
      List.flatten_append,p,List.append_assoc]

end ShiReversibleGenerator
