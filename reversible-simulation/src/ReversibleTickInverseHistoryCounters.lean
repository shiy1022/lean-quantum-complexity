import ReversibleTickInverseHistoryPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickInverseHistoryTemplate_capacity (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInverseHistoryTemplate tm bound).counters cs (.inl 1)=cs (.inl 1) := by
  change (tickInverseAdvanceIterationTemplate tm bound).counters
    ((tickInverseAdvanceStepTemplate tm 18 bound).counters ((tickHistoryCountTemplate tm).counters cs)) (.inl 1)=_
  rw [tickInverseAdvanceIterationTemplate_capacity,
    tickInverseAdvanceStepTemplate_control_frame tm 18 bound _ 1 (by decide) (by decide) (by decide),
    tickHistoryCountTemplate_counters]
  simp [tickTraversalSpare]

theorem tickInverseHistoryTemplate_count (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ht : 0 < cs (tickTraversalSpare tm 7)) :
    (tickInverseHistoryTemplate tm bound).counters cs (.inl 9)=cs (.inl 9)+
      cs (tickTraversalSpare tm 7)*tickForestLayerCount tm (cs (.inl 1)) := by
  change (tickInverseAdvanceIterationTemplate tm bound).counters
    ((tickInverseAdvanceStepTemplate tm 18 bound).counters ((tickHistoryCountTemplate tm).counters cs)) (.inl 9)=_
  rw [tickInverseAdvanceIterationTemplate_count,tickInverseAdvanceStepTemplate_count,
    tickInverseAdvanceStepTemplate_control_frame tm 18 bound _ 1 (by decide) (by decide) (by decide),
    tickInverseAdvanceStepTemplate_spare_frame tm 18 bound _ 3 (by decide) (by decide),tickHistoryCountTemplate_counters]
  simp only [Function.update_self,Function.update_of_ne (by simp [tickTraversalSpare] :
      (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
    Function.update_of_ne (by simp [tickTraversalSpare] :
      (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3)]
  have hn : (cs (tickTraversalSpare tm 7)-1+1)*tickForestLayerCount tm (cs (.inl 1))=
      cs (tickTraversalSpare tm 7)*tickForestLayerCount tm (cs (.inl 1)) :=
    congrArg (fun k => k*tickForestLayerCount tm (cs (.inl 1))) (Nat.sub_add_cancel (Nat.succ_le_of_lt ht))
  simp only [Nat.add_mul,Nat.one_mul] at hn
  omega

theorem tickInverseHistoryTemplate_output (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ht : 0 < cs (tickTraversalSpare tm 7)) :
    (tickInverseHistoryTemplate tm bound).counters cs (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2)+
      cs (tickTraversalSpare tm 7)*(configurationWidth tm (cs (.inl 1))*(bound+1)) := by
  change (tickInverseAdvanceIterationTemplate tm bound).counters
    ((tickInverseAdvanceStepTemplate tm 18 bound).counters ((tickHistoryCountTemplate tm).counters cs)) (tickTraversalSpare tm 2)=_
  rw [tickInverseAdvanceIterationTemplate_output,tickInverseAdvanceStepTemplate_output,
    tickInverseAdvanceStepTemplate_control_frame tm 18 bound _ 1 (by decide) (by decide) (by decide),
    tickInverseAdvanceStepTemplate_spare_frame tm 18 bound _ 3 (by decide) (by decide),tickHistoryCountTemplate_counters]
  simp only [Function.update_self,Function.update_of_ne (fun h =>
      (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)),
    Function.update_of_ne (by simp [tickTraversalSpare] :
      (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3)]
  have hn : (cs (tickTraversalSpare tm 7)-1+1)*(configurationWidth tm (cs (.inl 1))*(bound+1))=
      cs (tickTraversalSpare tm 7)*(configurationWidth tm (cs (.inl 1))*(bound+1)) :=
    congrArg (fun k => k*(configurationWidth tm (cs (.inl 1))*(bound+1))) (Nat.sub_add_cancel (Nat.succ_le_of_lt ht))
  simp only [Nat.add_mul,Nat.one_mul] at hn
  omega

theorem tickInverseHistoryTemplate_remaining (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInverseHistoryTemplate tm bound).counters cs (tickTraversalSpare tm 3)=0 := by
  change Function.update _ (tickTraversalSpare tm 3) 0 (tickTraversalSpare tm 3)=0
  exact Function.update_self _ _ _

theorem tickInverseHistoryTemplate_spare_frame (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) (h0 : j ≠ 0) (h2 : j ≠ 2) (h3 : j ≠ 3) :
    (tickInverseHistoryTemplate tm bound).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) := by
  let after := (tickInverseAdvanceStepTemplate tm 18 bound).counters ((tickHistoryCountTemplate tm).counters cs)
  have hj : tickTraversalSpare tm j ≠ tickTraversalSpare tm 3 := fun h => h3 (tickTraversalSpare_injective tm h)
  have hf := descendingProgramTemplate_point_frame (tickInverseAdvanceStepTemplate tm (bound+1) bound)
    (tickTraversalSpare tm 3) (tickTraversalSpare tm j) hj
    (fun t => tickInverseAdvanceStepTemplate_spare_frame tm (bound+1) bound t j h0 h2) after
  change (descendingProgramTemplate (tickInverseAdvanceStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3)).counters after (tickTraversalSpare tm j)=_
  rw [hf]
  dsimp only [after]
  rw [tickInverseAdvanceStepTemplate_spare_frame tm 18 bound _ j h0 h2,tickHistoryCountTemplate_counters,Function.update_of_ne hj]

end ShiReversibleGenerator
