import ReversibleExtractionCleanForestPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionInverseCleanForestDescending_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k : Nat) (cs : ExtractionForestRegister → Nat) :
    descendingTemplateCounters (extractionCleanForestStepTemplate tm e stride true) 26 k cs 16=cs 16+
      ((extractionOutputRange tm e (cs 0) (cs 1) k).map (fun p => formulaElementaryLayers p+1)).sum := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateCounters,extractionOutputRange]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionCleanForestStepTemplate tm e stride true).counters t
    have hm := extractionCleanForestStepTemplate_metadata tm e stride true t
    change u 0=t 0 ∧ u 1=t 1+1 ∧ u 11=t 11 ∧ u 18=t 18+t 27+1 ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht0 : t 0=cs 0 := by simp [t]
    have ht1 : t 1=cs 1 := by simp [t]
    have ht16 : t 16=cs 16 := by simp [t]
    have hc := extractionCleanForestStepTemplate_count tm e stride true t
    change u 16=_ at hc
    change descendingTemplateCounters _ 26 k u 16=_
    rw [ih,hc,hm.1,hm.2.1,ht0,ht1,ht16,extractionOutputRange_cons]
    simp only [List.map_cons,List.sum_cons]
    omega

theorem extractionInverseCleanForestLoopTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestLoopTemplate tm e stride true).counters cs 16=cs 16+
      ((extractionOutputRange tm e (cs 0) (cs 1) (cs 26)).map (fun p => formulaElementaryLayers p+1)).sum := by
  change Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 16=_
  rw [Function.update_of_ne (by decide : (16 : ExtractionForestRegister) ≠ 26)]
  exact extractionInverseCleanForestDescending_count tm e stride (cs 26) cs


theorem extractionForwardCleanForestDescending_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k : Nat) (cs : ExtractionForestRegister → Nat) (hj : cs 1=k-1) :
    descendingTemplateCounters (extractionCleanForestStepTemplate tm e stride false) 26 k cs 16=cs 16+
      ((extractionOutputRange tm e (cs 0) 0 k).map (fun p => formulaElementaryLayers p+1)).sum := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateCounters,extractionOutputRange]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionCleanForestStepTemplate tm e stride false).counters t
    have hm := extractionCleanForestStepTemplate_metadata tm e stride false t
    change u 0=t 0 ∧ u 1=t 1-1 ∧ u 11=t 11 ∧ u 18=t 18-(t 27+1) ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht0 : t 0=cs 0 := by simp [t]
    have ht1 : t 1=cs 1 := by simp [t]
    have ht16 : t 16=cs 16 := by simp [t]
    have hjk : cs 1=k := by omega
    have hu1 : u 1=k-1 := by rw [hm.2.1,ht1,hjk]
    have hc := extractionCleanForestStepTemplate_count tm e stride false t
    change u 16=_ at hc
    change descendingTemplateCounters _ 26 k u 16=_
    rw [ih u hu1,hc,hm.1,ht0,ht1,ht16,hjk,extractionOutputRange_snoc]
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
    omega

theorem extractionForwardCleanForestLoopTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionForestRegister → Nat) (hj : cs 1=cs 26-1) :
    (extractionCleanForestLoopTemplate tm e stride false).counters cs 16=cs 16+
      ((extractionOutputRange tm e (cs 0) 0 (cs 26)).map (fun p => formulaElementaryLayers p+1)).sum := by
  change Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 16=_
  rw [Function.update_of_ne (by decide : (16 : ExtractionForestRegister) ≠ 26)]
  exact extractionForwardCleanForestDescending_count tm e stride (cs 26) cs hj


end ShiReversibleGenerator
