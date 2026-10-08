import ReversibleTickPreparedForwardHistoryTemplate
import ReversibleTickPreparedForwardHistoryBudget
import ReversibleTickForwardHistoryCounters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickPreparedForwardHistoryState_capacity (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    tickPreparedForwardHistoryState tm bound cs (.inl 1)=cs (.inl 1) := by
  rw [tickPreparedForwardHistoryState,tickLateWindowTemplate_control_frame tm bound _ 1 (by decide),
    tickHistoryCountTemplate_counters]
  simp [tickTraversalSpare]

theorem tickPreparedForwardHistoryState_count (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    tickPreparedForwardHistoryState tm bound cs (.inl 9)=cs (.inl 9) := by
  rw [tickPreparedForwardHistoryState,tickLateWindowTemplate_control_frame tm bound _ 9 (by decide),
    tickHistoryCountTemplate_counters]
  simp [tickTraversalSpare]

theorem tickPreparedForwardHistoryTemplate_capacity (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickPreparedForwardHistoryTemplate tm bound).counters cs (.inl 1)=cs (.inl 1) := by
  change (tickForwardHistoryTemplate tm bound).counters (tickPreparedForwardHistoryState tm bound cs) (.inl 1)=_
  rw [tickForwardHistoryTemplate_capacity,tickPreparedForwardHistoryState_capacity]

theorem tickPreparedForwardHistoryTemplate_count (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ht : 0 < cs (tickTraversalSpare tm 7)) :
    (tickPreparedForwardHistoryTemplate tm bound).counters cs (.inl 9)=
      cs (.inl 9)+cs (tickTraversalSpare tm 7)*tickForestLayerCount tm (cs (.inl 1)) := by
  change (tickForwardHistoryTemplate tm bound).counters (tickPreparedForwardHistoryState tm bound cs) (.inl 9)=_
  rw [tickForwardHistoryTemplate_count,tickPreparedForwardHistoryState_count,tickPreparedForwardHistoryState_remaining,
    tickPreparedForwardHistoryState_capacity,Nat.sub_add_cancel (Nat.succ_le_of_lt ht)]

theorem tickPreparedForwardHistoryTemplate_remaining (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickPreparedForwardHistoryTemplate tm bound).counters cs (tickTraversalSpare tm 3)=0 :=
  tickForwardHistoryTemplate_remaining tm bound (tickPreparedForwardHistoryState tm bound cs)

theorem tickPreparedForwardHistoryTemplate_output (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickPreparedForwardHistoryTemplate tm bound).counters cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 6)+18*configurationWidth tm (cs (.inl 1)) := by
  change (tickForwardHistoryTemplate tm bound).counters (tickPreparedForwardHistoryState tm bound cs) (tickTraversalSpare tm 2)=_
  rw [tickForwardHistoryTemplate_output,tickPreparedForwardHistoryState_raw_length,tickPreparedForwardHistoryState_capacity]

end ShiReversibleGenerator
