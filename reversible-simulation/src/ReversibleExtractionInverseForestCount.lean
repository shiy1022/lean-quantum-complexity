import ReversibleExtractionForestLoop
import ReversibleExtractionForestStepPayload
import ReversibleExtractionOutputRange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The inverse output forest counts each original formula and its output-root copy exactly once. -/
theorem extractionInverseForestDescending_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k : Nat) (cs : ExtractionForestRegister → Nat) :
    descendingTemplateCounters (extractionForestStepTemplate tm e stride true) 26 k cs 16=cs 16+
      ((extractionOutputRange tm e (cs 0) (cs 1) k).map (fun p => formulaElementaryLayers p+1)).sum := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateCounters,extractionOutputRange]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionForestStepTemplate tm e stride true).counters t
    have hm := extractionForestStepTemplate_metadata tm e stride true t
    change u 0=t 0 ∧ u 1=t 1+1 ∧ u 11=t 11 ∧ u 18=t 18+t 27+1 ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht0 : t 0=cs 0 := by simp [t]
    have ht1 : t 1=cs 1 := by simp [t]
    have ht16 : t 16=cs 16 := by simp [t]
    have hc := extractionForestStepTemplate_count tm e stride true t
    change u 16=_ at hc
    change descendingTemplateCounters _ 26 k u 16=_
    rw [ih,hc,hm.1,hm.2.1,ht0,ht1,ht16,extractionOutputRange_cons]
    simp only [List.map_cons,List.sum_cons]
    omega

theorem extractionInverseForestLoopTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionForestRegister → Nat) :
    (extractionForestLoopTemplate tm e stride true).counters cs 16=cs 16+
      ((extractionOutputRange tm e (cs 0) (cs 1) (cs 26)).map (fun p => formulaElementaryLayers p+1)).sum := by
  change Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 16=_
  rw [Function.update_of_ne (by decide : (16 : ExtractionForestRegister) ≠ 26)]
  exact extractionInverseForestDescending_count tm e stride (cs 26) cs

end ShiReversibleGenerator
