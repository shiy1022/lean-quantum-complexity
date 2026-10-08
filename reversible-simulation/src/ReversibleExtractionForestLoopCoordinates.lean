import ReversibleExtractionForestLoopFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The recursive emitter moves exactly one output position and one fixed-width slot per body execution. -/
theorem extractionForestDescending_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (k : Nat) (cs : ExtractionForestRegister → Nat) :
    let after := descendingTemplateCounters (extractionForestStepTemplate tm e stride backward) 26 k cs
    after 1=(if backward then cs 1+k else cs 1-k) ∧
      after 18=(if backward then cs 18+k*(cs 27+1) else cs 18-k*(cs 27+1)) := by
  induction k generalizing cs with
  | zero => cases backward <;> simp [descendingTemplateCounters]
  | succ k ih =>
    let t := Function.update cs (26 : ExtractionForestRegister) k
    let u := (extractionForestStepTemplate tm e stride backward).counters t
    have hm := extractionForestStepTemplate_metadata tm e stride backward t
    change u 0=t 0 ∧ u 1=(if backward then t 1+1 else t 1-1) ∧ u 11=t 11 ∧
      u 18=(if backward then t 18+t 27+1 else t 18-(t 27+1)) ∧ u 26=t 26 ∧ u 27=t 27 at hm
    have ht1 : t 1=cs 1 := by simp [t]
    have ht18 : t 18=cs 18 := by simp [t]
    have ht27 : t 27=cs 27 := by simp [t]
    change (descendingTemplateCounters _ 26 k u) 1=_ ∧ (descendingTemplateCounters _ 26 k u) 18=_
    rw [(ih u).1,(ih u).2,hm.2.1,hm.2.2.2.1,hm.2.2.2.2.2,ht1,ht18,ht27]
    cases backward <;> simp [Nat.add_mul,Nat.sub_sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem extractionForestLoopTemplate_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    let after := (extractionForestLoopTemplate tm e stride backward).counters cs
    after 1=(if backward then cs 1+cs 26 else cs 1-cs 26) ∧
      after 18=(if backward then cs 18+cs 26*(cs 27+1) else cs 18-cs 26*(cs 27+1)) := by
  change Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 1=_ ∧
    Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 18=_
  rw [Function.update_of_ne (by decide : (1 : ExtractionForestRegister) ≠ 26),
    Function.update_of_ne (by decide : (18 : ExtractionForestRegister) ≠ 26)]
  exact extractionForestDescending_coordinates tm e stride backward (cs 26) cs

end ShiReversibleGenerator
