import ReversibleExtractionForestLoop
import ReversibleExtractionForestStepPayload
import ReversibleExtractionOutputRange
import ReversiblePaddedForestSnoc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Descending emission prepends slots into the original increasing padded forest order. -/
theorem extractionForwardForestDescending_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k base : Nat) (cs : ExtractionForestRegister → Nat)
    (hj : cs 1=k-1) (hb : cs 18=base+k*(cs 27+1)) :
    descendingTemplateBytes (extractionForestStepTemplate tm e stride false) 26 k cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) base (cs 27)
        (extractionOutputRange tm e (cs 0) 0 k)).map (rawAssignmentPayload false)).flatten := by
  induction k generalizing base cs with
  | zero => simp [descendingTemplateBytes,extractionOutputRange,paddedForestCompile]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionForestStepTemplate tm e stride false).counters t
    have hm := extractionForestStepTemplate_metadata tm e stride false t
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
    change descendingTemplateBytes _ 26 k u ++ (extractionForestStepTemplate tm e stride false).bytes t=_
    rw [ih base u hu1 hu18,extractionForestStepTemplate_payload,hm.1,hm.2.2.1,hm.2.2.2.2.2,
      ht0,ht1,ht11,ht18,ht27,hjk,hslot,extractionOutputRange_snoc,paddedForestCompile_snoc]
    simp [extractionOutputRange,List.map_append,List.flatten_append]

theorem extractionForwardForestLoopTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride base : Nat) (cs : ExtractionForestRegister → Nat)
    (hj : cs 1=cs 26-1) (hb : cs 18=base+cs 26*(cs 27+1)) :
    (extractionForestLoopTemplate tm e stride false).bytes cs=
      ((paddedForestCompile (fun i => cs 11+stride*i.val) base (cs 27)
        (extractionOutputRange tm e (cs 0) 0 (cs 26))).map (rawAssignmentPayload false)).flatten :=
  extractionForwardForestDescending_payload tm e stride (cs 26) base cs hj hb

end ShiReversibleGenerator
