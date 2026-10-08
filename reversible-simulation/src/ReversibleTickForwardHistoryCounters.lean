import ReversibleTickForwardHistoryReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickForwardHistoryTemplate_capacity (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardHistoryTemplate tm bound).counters cs (.inl 1)=cs (.inl 1) := by
  change (tickForestTemplate tm 18 bound false).counters
    ((tickInitializedWindowTemplate tm).counters ((tickRetreatIterationTemplate tm bound).counters cs)) (.inl 1)=_
  rw [tickForestTemplate_control_frame tm 18 bound false _ 1 (by decide) (by decide),
    tickInitializedWindowTemplate_control_frame tm _ 1 (by decide),tickRetreatIterationTemplate_capacity]

theorem tickForwardHistoryTemplate_count (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardHistoryTemplate tm bound).counters cs (.inl 9)=
      cs (.inl 9)+(cs (tickTraversalSpare tm 3)+1)*tickForestLayerCount tm (cs (.inl 1)) := by
  change (tickForestTemplate tm 18 bound false).counters
    ((tickInitializedWindowTemplate tm).counters ((tickRetreatIterationTemplate tm bound).counters cs)) (.inl 9)=_
  rw [tickForestTemplate_count,tickInitializedWindowTemplate_control_frame tm _ 9 (by decide),
    tickInitializedWindowTemplate_control_frame tm _ 1 (by decide),
    tickRetreatIterationTemplate_count,tickRetreatIterationTemplate_capacity]
  simp only [Nat.add_mul,Nat.one_mul,Nat.add_assoc]

theorem tickForwardHistoryTemplate_remaining (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardHistoryTemplate tm bound).counters cs (tickTraversalSpare tm 3)=0 := by
  change (tickForestTemplate tm 18 bound false).counters
    ((tickInitializedWindowTemplate tm).counters ((tickRetreatIterationTemplate tm bound).counters cs)) (tickTraversalSpare tm 3)=_
  rw [tickForestTemplate_spare_frame tm 18 bound false _ 3 (by decide),tickInitializedWindowTemplate_counters]
  rw [Function.update_of_ne (fun h => (by decide : (3 : Fin 8) ≠ 2) (tickTraversalSpare_injective tm h)),
    Function.update_of_ne (by simp [tickTraversalSpare])]
  change Function.update _ (tickTraversalSpare tm 3) 0 (tickTraversalSpare tm 3)=0
  exact Function.update_self _ _ _

theorem tickForwardHistoryTemplate_output (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardHistoryTemplate tm bound).counters cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 6)+18*configurationWidth tm (cs (.inl 1)) := by
  change (tickForestTemplate tm 18 bound false).counters
    ((tickInitializedWindowTemplate tm).counters ((tickRetreatIterationTemplate tm bound).counters cs)) (tickTraversalSpare tm 2)=_
  rw [tickForestTemplate_spare_frame tm 18 bound false _ 2 (by decide),tickInitializedWindowTemplate_output,
    tickRetreatIterationTemplate_spare_frame tm bound cs 6 (by decide) (by decide) (by decide) (by decide),
    tickRetreatIterationTemplate_capacity]

end ShiReversibleGenerator
