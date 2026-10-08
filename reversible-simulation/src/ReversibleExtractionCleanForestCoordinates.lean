import ReversibleExtractionCleanForestLoop
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionCleanForestLoopTemplate_source_frames (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    let after := (extractionCleanForestLoopTemplate tm e stride backward).counters cs
    after 0=cs 0 ∧ after 11=cs 11 ∧ after 27=cs 27 := by
  refine ⟨?_,?_,?_⟩
  · exact descendingProgramTemplate_point_frame _ 26 0 (by decide)
      (fun t => (extractionCleanForestStepTemplate_metadata tm e stride backward t).1) cs
  · exact descendingProgramTemplate_point_frame _ 26 11 (by decide)
      (fun t => (extractionCleanForestStepTemplate_metadata tm e stride backward t).2.2.1) cs
  · exact descendingProgramTemplate_point_frame _ 26 27 (by decide)
      (fun t => (extractionCleanForestStepTemplate_metadata tm e stride backward t).2.2.2.2.2) cs

theorem extractionCleanForestLoopTemplate_remaining (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestLoopTemplate tm e stride backward).counters cs 26=0 := by
  simp [extractionCleanForestLoopTemplate,descendingProgramTemplate]


theorem extractionCleanForestDescending_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (k : Nat) (cs : ExtractionForestRegister → Nat) :
    let after := descendingTemplateCounters (extractionCleanForestStepTemplate tm e stride backward) 26 k cs
    after 1=(if backward then cs 1+k else cs 1-k) ∧
      after 18=(if backward then cs 18+k*(cs 27+1) else cs 18-k*(cs 27+1)) := by
  induction k generalizing cs with
  | zero => cases backward <;> simp [descendingTemplateCounters]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionCleanForestStepTemplate tm e stride backward).counters t
    have hm := extractionCleanForestStepTemplate_metadata tm e stride backward t
    change u 0=t 0 ∧ u 1=(if backward then t 1+1 else t 1-1) ∧ u 11=t 11 ∧
      u 18=(if backward then t 18+t 27+1 else t 18-(t 27+1)) ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht1 : t 1=cs 1 := by simp [t]
    have ht18 : t 18=cs 18 := by simp [t]
    have ht27 : t 27=cs 27 := by simp [t]
    change (descendingTemplateCounters _ 26 k u) 1=_ ∧ (descendingTemplateCounters _ 26 k u) 18=_
    rw [(ih u).1,(ih u).2,hm.2.1,hm.2.2.2.1,hm.2.2.2.2.2,ht1,ht18,ht27]
    cases backward <;> simp [Nat.add_mul,Nat.sub_sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem extractionCleanForestLoopTemplate_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    let after := (extractionCleanForestLoopTemplate tm e stride backward).counters cs
    after 1=(if backward then cs 1+cs 26 else cs 1-cs 26) ∧
      after 18=(if backward then cs 18+cs 26*(cs 27+1) else cs 18-cs 26*(cs 27+1)) := by
  change Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 1=_ ∧
    Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 18=_
  rw [Function.update_of_ne (by decide : (1 : ExtractionForestRegister) ≠ 26),
    Function.update_of_ne (by decide : (18 : ExtractionForestRegister) ≠ 26)]
  exact extractionCleanForestDescending_coordinates tm e stride backward (cs 26) cs


end ShiReversibleGenerator
