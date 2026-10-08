import ReversibleExtractionInverseClosingTraversalMetadata
import ReversibleExtractionInverseClosingStepPayload
import ReversibleExtractionClosingSuffixSnoc
import ReversibleExtractionNaturalTermRangeSnoc

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Descending selected terms and ascending suffix endpoints emit exactly the reversed original closing pass. -/
theorem extractionInverseClosingLoop_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (k start base : Nat) (cs : ExtractionTraversalRegister → Nat)
    (hell : cs 2=start+k-1) (hlimit : start+k ≤ cs 0+1)
    (hbase : cs 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) start k).map (fun p => p.size+1)).sum)
    (hend : 3 ≤ cs 20) :
    descendingTemplateBytes (extractionInverseClosingTraversalStepTemplate tm) 22 k cs=
      (((disjoinClosingSuffix base (cs 20+3*k-3)
        (extractionNaturalTermRange tm e (cs 0) (cs 1) start k)).reverse).map
        (rawAssignmentPayload true)).flatten := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateBytes,extractionNaturalTermRange,disjoinClosingSuffix]
  | succ k ih =>
    let next := Function.update cs (22 : ExtractionTraversalRegister) k
    let after := (extractionInverseClosingTraversalStepTemplate tm).counters next
    let p := extractionNaturalTerm tm e (cs 0) (start+k) (cs 1)
    let firstTerms := extractionNaturalTermRange tm e (cs 0) (cs 1) start k
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=start+k := by simp [next,hell]
    have hn18 : next 18=cs 18 := by simp [next]
    have hn20 : next 20=cs 20 := by simp [next]
    have h0 : after 0=cs 0 := (extractionInverseClosingTraversalStepTemplate_metadata tm next).1.trans hn0
    have h1 : after 1=cs 1 := (extractionInverseClosingTraversalStepTemplate_metadata tm next).2.1.trans hn1
    have h2 : after 2=start+k-1 := by
      have h := (extractionInverseClosingTraversalStepTemplate_metadata tm next).2.2.1
      rw [hn2] at h
      exact h
    have h20 : after 20=cs 20+3 := by
      have h := (extractionInverseClosingTraversalStepTemplate_metadata tm next).2.2.2.2
      rw [hn20] at h
      exact h
    have hpSize : p.size+4=extractionSizeContribution tm (start+k) (cs 1) :=
      extractionNaturalTerm_size tm e (cs 0) (start+k) (cs 1) (by omega)
    have hb : cs 18=base+((firstTerms.map (fun p => p.size+1)).sum+(p.size+1)) := by
      rw [extractionNaturalTermRange_snoc] at hbase
      simpa only [firstTerms,p,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using hbase
    have h18 : after 18=base+(firstTerms.map (fun p => p.size+1)).sum := by
      have h := (extractionInverseClosingTraversalStepTemplate_metadata tm next).2.2.2.1
      rw [hn18,hn2,hn1,←hpSize] at h
      change after 18=cs 18-(p.size+4-3) at h
      omega
    have hi := ih after h2 (by rw [h0]; omega)
      (by simpa only [h0,h1,firstTerms] using h18) (by rw [h20]; omega)
    rw [h0,h1,h20] at hi
    have he : cs 20+3+3*k-3=cs 20+3*k := by omega
    rw [he] at hi
    have hp : (extractionInverseClosingTraversalStepTemplate tm).bytes next=
        ([RawAssignment.neg (cs 20-3) (cs 20-2),
          .conj (base+(firstTerms.map (fun p => p.size+1)).sum+p.size) (cs 20-2) (cs 20-1),
          .neg (cs 20-1) (cs 20)].reverse.map (rawAssignmentPayload true)).flatten := by
      let small := fun r => next (extractionTermToTraversalRegister r)
      have hs0 : small 0=cs 0 := hn0
      have hs1 : small 1=cs 1 := hn1
      have hs2 : small 2=start+k := hn2
      have hs18 : small 18=cs 18 := hn18
      have hs20 : small 20=cs 20 := hn20
      have h := extractionInverseClosingStepTemplate_payload tm e small
        (by rw [hs2,hs0]; omega) (by rw [hs20]; exact hend)
      change (extractionInverseClosingTraversalStepTemplate tm).bytes next=_ at h
      have he18 : cs 18-(extractionSizeContribution tm (start+k) (cs 1)-3)=
          base+(firstTerms.map (fun p => p.size+1)).sum := by rw [←hpSize]; omega
      exact h.trans (by
        rw [hs0,hs1,hs2,hs18,hs20,he18]
        simp only [p,extractionNaturalTerm,Formula.rename_size])
    rw [descendingTemplateBytes]
    change descendingTemplateBytes (extractionInverseClosingTraversalStepTemplate tm) 22 k after ++
      (extractionInverseClosingTraversalStepTemplate tm).bytes next=_
    rw [hi,hp,extractionNaturalTermRange_snoc]
    have he' : cs 20+3*(k+1)-3=cs 20+3*k := by omega
    rw [he',disjoinClosingSuffix_snoc,extractionNaturalTermRange_length]
    have he'' : cs 20+3*k-3*k=cs 20 := by omega
    simp only [he'',List.reverse_append,List.map_append,List.flatten_append,firstTerms,p]

end ShiReversibleGenerator
