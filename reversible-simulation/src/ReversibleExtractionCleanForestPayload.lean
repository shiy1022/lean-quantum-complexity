import ReversibleExtractionCleanForestLoop
import ReversibleExtractionOutputRange
import ReversiblePaddedForestSnoc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionCleanForestStepTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestStepTemplate tm e stride backward).bytes cs=
      ((if backward then ((extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18) (cs 27)).reverse
        else (extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18-(cs 27+1)) (cs 27)).map (rawAssignmentPayload backward)).flatten  := by
  rw [extractionCleanForestStepTemplate_bytes]
  exact extractionForestStepTemplate_payload tm e stride backward cs

theorem extractionInverseCleanForestDescending_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k : Nat) (cs : ExtractionForestRegister → Nat) :
    descendingTemplateBytes (extractionCleanForestStepTemplate tm e stride true) 26 k cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) (cs 18) (cs 27)
        (extractionOutputRange tm e (cs 0) (cs 1) k)).reverse.map (rawAssignmentPayload true)).flatten := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateBytes,extractionOutputRange,paddedForestCompile]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionCleanForestStepTemplate tm e stride true).counters t
    have hm := extractionCleanForestStepTemplate_metadata tm e stride true t
    change u 0=t 0 ∧ u 1=t 1+1 ∧ u 11=t 11 ∧ u 18=t 18+t 27+1 ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht0 : t 0=cs 0 := by simp [t]
    have ht1 : t 1=cs 1 := by simp [t]
    have ht11 : t 11=cs 11 := by simp [t]
    have ht18 : t 18=cs 18 := by simp [t]
    have ht27 : t 27=cs 27 := by simp [t]
    change descendingTemplateBytes _ 26 k u ++ (extractionCleanForestStepTemplate tm e stride true).bytes t=_
    rw [ih,extractionCleanForestStepTemplate_payload,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2.2,
      ht0,ht1,ht11,ht18,ht27,extractionOutputRange_cons]
    simp [paddedForestCompile,List.reverse_append,List.map_append,List.flatten_append,Nat.add_assoc]

theorem extractionInverseCleanForestLoopTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestLoopTemplate tm e stride true).bytes cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) (cs 18) (cs 27)
        (extractionOutputRange tm e (cs 0) (cs 1) (cs 26))).reverse.map (rawAssignmentPayload true)).flatten :=
  extractionInverseCleanForestDescending_payload tm e stride (cs 26) cs


theorem extractionForwardCleanForestDescending_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k base : Nat) (cs : ExtractionForestRegister → Nat)
    (hj : cs 1=k-1) (hb : cs 18=base+k*(cs 27+1)) :
    descendingTemplateBytes (extractionCleanForestStepTemplate tm e stride false) 26 k cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) base (cs 27)
        (extractionOutputRange tm e (cs 0) 0 k)).map (rawAssignmentPayload false)).flatten := by
  induction k generalizing base cs with
  | zero => simp [descendingTemplateBytes,extractionOutputRange,paddedForestCompile]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionCleanForestStepTemplate tm e stride false).counters t
    have hm := extractionCleanForestStepTemplate_metadata tm e stride false t
    change u 0=t 0 ∧ u 1=t 1-1 ∧ u 11=t 11 ∧ u 18=t 18-(t 27+1) ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht0 : t 0=cs 0 := by simp [t]
    have ht1 : t 1=cs 1 := by simp [t]
    have ht11 : t 11=cs 11 := by simp [t]
    have ht18 : t 18=cs 18 := by simp [t]
    have ht27 : t 27=cs 27 := by simp [t]
    have hjk : cs 1=k := by omega
    have hslot : cs 18-(cs 27+1)=base+k*(cs 27+1) := by
      rw [hb,Nat.add_mul]
      simp only [Nat.one_mul]
      omega
    have hu1 : u 1=k-1 := by rw [hm.2.1,ht1,hjk]
    have hu18 : u 18=base+k*(u 27+1) := by rw [hm.2.2.2.1,hm.2.2.2.2.2,ht18,ht27,hslot]
    change descendingTemplateBytes _ 26 k u ++ (extractionCleanForestStepTemplate tm e stride false).bytes t=_
    rw [ih base u hu1 hu18,extractionCleanForestStepTemplate_payload,hm.1,hm.2.2.1,hm.2.2.2.2.2,
      ht0,ht1,ht11,ht18,ht27,hjk,hslot,extractionOutputRange_snoc,paddedForestCompile_snoc]
    simp [extractionOutputRange,List.map_append,List.flatten_append]

theorem extractionForwardCleanForestLoopTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride base : Nat) (cs : ExtractionForestRegister → Nat)
    (hj : cs 1=cs 26-1) (hb : cs 18=base+cs 26*(cs 27+1)) :
    (extractionCleanForestLoopTemplate tm e stride false).bytes cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) base (cs 27)
        (extractionOutputRange tm e (cs 0) 0 (cs 26))).map (rawAssignmentPayload false)).flatten :=
  extractionForwardCleanForestDescending_payload tm e stride (cs 26) base cs hj hb


end ShiReversibleGenerator
