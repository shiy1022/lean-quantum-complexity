import ReversibleExtractionForestLoop
import ReversibleExtractionForestStepPayload
import ReversibleExtractionOutputRange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Actual ascending inverse emission agrees with the reverse of the original padded forest. -/
theorem extractionInverseForestDescending_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k : Nat) (cs : ExtractionForestRegister → Nat) :
    descendingTemplateBytes (extractionForestStepTemplate tm e stride true) 26 k cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) (cs 18) (cs 27)
        (extractionOutputRange tm e (cs 0) (cs 1) k)).reverse.map (rawAssignmentPayload true)).flatten := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateBytes,extractionOutputRange,paddedForestCompile]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionForestStepTemplate tm e stride true).counters t
    have hm := extractionForestStepTemplate_metadata tm e stride true t
    change u 0=t 0 ∧ u 1=t 1+1 ∧ u 11=t 11 ∧ u 18=t 18+t 27+1 ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht0 : t 0=cs 0 := by simp [t]
    have ht1 : t 1=cs 1 := by simp [t]
    have ht11 : t 11=cs 11 := by simp [t]
    have ht18 : t 18=cs 18 := by simp [t]
    have ht27 : t 27=cs 27 := by simp [t]
    change descendingTemplateBytes _ 26 k u ++ (extractionForestStepTemplate tm e stride true).bytes t=_
    rw [ih,extractionForestStepTemplate_payload,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2.2,
      ht0,ht1,ht11,ht18,ht27,extractionOutputRange_cons]
    simp [paddedForestCompile,List.reverse_append,List.map_append,List.flatten_append,Nat.add_assoc]

theorem extractionInverseForestLoopTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionForestRegister → Nat) :
    (extractionForestLoopTemplate tm e stride true).bytes cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) (cs 18) (cs 27)
        (extractionOutputRange tm e (cs 0) (cs 1) (cs 26))).reverse.map (rawAssignmentPayload true)).flatten :=
  extractionInverseForestDescending_payload tm e stride (cs 26) cs

end ShiReversibleGenerator
