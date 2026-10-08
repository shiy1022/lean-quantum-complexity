import ReversibleTickRetreatIterationTemplate
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickRetreatIterationTemplate_capacity (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickRetreatIterationTemplate tm bound).counters cs (.inl 1)=cs (.inl 1) := by
  apply descendingProgramTemplate_point_frame
  · simp [tickTraversalSpare]
  · intro t
    exact tickRetreatStepTemplate_control_frame tm (bound+1) bound t 1 (by decide) (by decide) (by decide)

theorem tickRetreatIterationCounters_count (tm : Turing.FinTM2) (bound k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    descendingTemplateCounters (tickRetreatStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3) k cs (.inl 9)=
      cs (.inl 9)+k*tickForestLayerCount tm (cs (.inl 1)) := by
  induction k generalizing cs with
  | zero => simp only [descendingTemplateCounters,Nat.zero_mul,Nat.add_zero,Nat.sub_zero]
  | succ k ih =>
    rw [descendingTemplateCounters,ih,tickRetreatStepTemplate_count,
      tickRetreatStepTemplate_control_frame tm (bound+1) bound _ 1 (by decide) (by decide) (by decide)]
    simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
      (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
      Function.update_of_ne (by simp [tickTraversalSpare] :
      (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),Nat.succ_mul,Nat.sub_sub]
    omega

theorem tickRetreatIterationTemplate_count (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickRetreatIterationTemplate tm bound).counters cs (.inl 9)=cs (.inl 9)+
      cs (tickTraversalSpare tm 3)*tickForestLayerCount tm (cs (.inl 1)) := by
  change Function.update (descendingTemplateCounters _ _ _ cs) (tickTraversalSpare tm 3) 0 (.inl 9)=_
  rw [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
    tickRetreatIterationCounters_count]

theorem tickRetreatIterationCounters_output (tm : Turing.FinTM2) (bound k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    descendingTemplateCounters (tickRetreatStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3) k cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 2)-k*(configurationWidth tm (cs (.inl 1))*(bound+1)) := by
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h =>
    (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  induction k generalizing cs with
  | zero => simp only [descendingTemplateCounters,Nat.zero_mul,Nat.add_zero,Nat.sub_zero]
  | succ k ih =>
    rw [descendingTemplateCounters,ih,tickRetreatStepTemplate_output,
      tickRetreatStepTemplate_control_frame tm (bound+1) bound _ 1 (by decide) (by decide) (by decide)]
    simp only [Function.update_of_ne h23,Function.update_of_ne (by simp [tickTraversalSpare] :
      (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),Nat.succ_mul,Nat.sub_sub]
    omega

theorem tickRetreatIterationTemplate_output (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickRetreatIterationTemplate tm bound).counters cs (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2)-
      cs (tickTraversalSpare tm 3)*(configurationWidth tm (cs (.inl 1))*(bound+1)) := by
  change Function.update (descendingTemplateCounters _ _ _ cs) (tickTraversalSpare tm 3) 0 (tickTraversalSpare tm 2)=_
  rw [Function.update_of_ne (fun h => (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)),
    tickRetreatIterationCounters_output]

end ShiReversibleGenerator
