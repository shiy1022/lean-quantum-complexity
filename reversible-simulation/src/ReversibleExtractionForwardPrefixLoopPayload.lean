import ReversibleExtractionForwardPrefixTraversalMetadata
import ReversibleExtractionForwardPrefixNaturalPayload
import ReversibleExtractionNaturalTermRangeSnoc
import ReversibleExtractionDisjoinPrefixSplit

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual descending prefix pass emits the original ascending compiler list. -/
theorem extractionForwardPrefixLoop_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (k : Nat) (cs : ExtractionTraversalRegister → Nat) (base : Nat)
    (hk : k ≤ cs 0+1) (hell : cs 2=k-1)
    (hend : cs 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 k).map (fun p => p.size+1)).sum) :
    descendingTemplateBytes (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k cs=
      ((disjoinTermPrefix (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit) base
        (extractionNaturalTermRange tm e (cs 0) (cs 1) 0 k)).map (rawAssignmentPayload false)).flatten := by
  induction k generalizing cs base with
  | zero => simp [descendingTemplateBytes,extractionNaturalTermRange,disjoinTermPrefix]
  | succ k ih =>
    let next := Function.update cs (22 : ExtractionTraversalRegister) k
    let after := (extractionForwardPrefixTraversalStepTemplate tm e stride).counters next
    let small : ExtractionTermRegister → Nat := fun r => next (extractionTermToTraversalRegister r)
    let ps := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 k
    let p := extractionNaturalTerm tm e (cs 0) k (cs 1)
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=k := by simpa [next] using hell
    have hn11 : next 11=cs 11 := by simp [next]
    have hn18 : next 18=cs 18 := by simp [next]
    have hs0 : small 0=cs 0 := hn0
    have hs1 : small 1=cs 1 := hn1
    have hs2 : small 2=k := hn2
    have hs11 : small 11=cs 11 := hn11
    have hs18 : small 18=cs 18 := hn18
    have hm := extractionForwardPrefixTraversalStepTemplate_metadata tm e stride next
    dsimp only at hm
    rw [hn0,hn1,hn2,hn11,hn18] at hm
    have ha0 : after 0=cs 0 := hm.1
    have ha1 : after 1=cs 1 := hm.2.1
    have ha11 : after 11=cs 11 := hm.2.2.1
    have ha2 : after 2=k-1 := hm.2.2.2.1
    have hc : extractionSizeContribution tm k (cs 1)=p.size+4 :=
      (extractionNaturalTerm_size tm e (cs 0) k (cs 1) (by omega)).symm
    have hsnoc : extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (k+1)=ps++[p] := by
      simpa only [Nat.zero_add,ps,p] using extractionNaturalTermRange_snoc tm e (cs 0) (cs 1) 0 k
    have he : cs 18=base+(ps.map (fun p => p.size+1)).sum+(p.size+1) := by
      rw [hsnoc] at hend
      simpa only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,Nat.add_assoc] using hend
    have hb : cs 18-(p.size+1)=base+(ps.map (fun p => p.size+1)).sum := by omega
    have ha18 : after 18=base+(ps.map (fun p => p.size+1)).sum := by
      have h := hm.2.2.2.2
      rw [hc] at h
      change after 18=cs 18-(p.size+4-3) at h
      omega
    have hi := ih after base (by rw [ha0]; omega) ha2 (by rw [ha0,ha1]; exact ha18)
    rw [ha0,ha11,ha1] at hi
    have hp := extractionForwardPrefixStepTemplate_natural_payload tm e stride small (by rw [hs2,hs0]; omega)
    dsimp only at hp
    rw [hs0,hs1,hs2,hs11,hs18,hb] at hp
    rw [descendingTemplateBytes]
    change descendingTemplateBytes (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k after ++
      (extractionForwardPrefixTraversalStepTemplate tm e stride).bytes next=_
    rw [hi]
    change _ ++ (extractionForwardPrefixStepTemplate tm e stride).bytes small=_
    rw [hp,hsnoc,disjoinTermPrefix_snoc]
    simp only [disjoinFalseBase_exact,List.map_append,List.flatten_append,ps,p]

end ShiReversibleGenerator
