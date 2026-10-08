import ReversibleExtractionClosingStepMetadata
import ReversibleExtractionClosingStepFrames
import ReversibleExtractionForwardClosingLoop
import ReversibleExtractionNaturalTermRange

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The real ascending-index loop prepends closing groups in exactly the original compiler's right-fold order. -/
theorem extractionForwardClosing_descending_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (k : Nat) (cs : ExtractionTermRegister → Nat) (hlimit : cs 2+k ≤ cs 0+1)
    (hend : cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) k).map (fun p => p.size+4)).sum) :
    descendingTemplateBytes (extractionClosingStepTemplate tm false) 9 k cs=
      ((disjoinClosingSuffix (cs 18) (cs 20) (extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) k)).map
        (rawAssignmentPayload false)).flatten := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateBytes,extractionNaturalTermRange,disjoinClosingSuffix]
  | succ k ih =>
    let next := Function.update cs 9 k
    let after := (extractionClosingStepTemplate tm false).counters next
    let p := extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1)
    let tail := extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2+1) k
    have hn0 : next 0=cs 0 := by simp only [next,Function.update_of_ne (by decide : (0 : ExtractionTermRegister) ≠ 9)]
    have hn1 : next 1=cs 1 := by simp only [next,Function.update_of_ne (by decide : (1 : ExtractionTermRegister) ≠ 9)]
    have hn2 : next 2=cs 2 := by simp only [next,Function.update_of_ne (by decide : (2 : ExtractionTermRegister) ≠ 9)]
    have hn18 : next 18=cs 18 := by simp only [next,Function.update_of_ne (by decide : (18 : ExtractionTermRegister) ≠ 9)]
    have hn20 : next 20=cs 20 := by simp only [next,Function.update_of_ne (by decide : (20 : ExtractionTermRegister) ≠ 9)]
    have hell : next 2 ≤ next 0 := by rw [hn2,hn0]; omega
    have hframe : ∀ q ∈ ([0,1] : List ExtractionTermRegister),after q=cs q := by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq | hq
      · subst q
        exact (extractionClosingStepTemplate_frame tm false next 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn0
      · subst q
        exact (extractionClosingStepTemplate_frame tm false next 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn1
    have h0 := hframe 0 (by simp)
    have h1 := hframe 1 (by simp)
    have h2 : after 2=cs 2+1 := by
      have h := (extractionClosingStepTemplate_metadata tm false next).1
      rw [hn2] at h
      exact h
    have h18 : after 18=cs 18+p.size+1 := by
      have h := extractionClosingStepTemplate_termBase tm e false next hell
      rw [hn0,hn1,hn2,hn18] at h
      simpa only [p,extractionNaturalTerm,Formula.rename_size] using h
    have h20 : after 20=cs 20-3 := by
      have h := (extractionClosingStepTemplate_metadata tm false next).2.2
      rw [hn20] at h
      exact h
    have he : cs 20=cs 18+(p.size+4+(tail.map (fun q => q.size+4)).sum) := by
      simpa only [extractionNaturalTermRange,List.map_cons,List.sum_cons,p,tail] using hend
    have hpos : 3 ≤ next 20 := by rw [hn20]; omega
    have hlim' : after 2+k ≤ after 0+1 := by rw [h2,h0]; omega
    have hend' : after 20=after 18+((extractionNaturalTermRange tm e (after 0) (after 1) (after 2) k).map (fun q => q.size+4)).sum := by
      rw [h20,h18,h0,h1,h2]
      change cs 20-3=cs 18+p.size+1+(tail.map (fun q => q.size+4)).sum
      omega
    have ht := ih after hlim' hend'
    rw [h0,h1,h2,h18,h20] at ht
    have hp : (extractionClosingStepTemplate tm false).bytes next=
        ([RawAssignment.neg (cs 20-3) (cs 20-2),.conj (cs 18+p.size) (cs 20-2) (cs 20-1),
          .neg (cs 20-1) (cs 20)].map (rawAssignmentPayload false)).flatten := by
      rw [extractionClosingStepTemplate_bytes]
      have h := extractionBoundClosingPrinterTemplate_payload tm e false next hell hpos
      dsimp only at h
      rw [hn0,hn1,hn2,hn18,hn20] at h
      simpa [p,extractionNaturalTerm,Formula.rename_size] using h
    rw [descendingTemplateBytes]
    change descendingTemplateBytes (extractionClosingStepTemplate tm false) 9 k after ++
      (extractionClosingStepTemplate tm false).bytes next = _
    rw [ht,hp]
    simp only [extractionNaturalTermRange,disjoinClosingSuffix,List.map_append,List.flatten_append,p]

end ShiReversibleGenerator
