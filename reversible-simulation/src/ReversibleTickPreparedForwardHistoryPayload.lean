import ReversibleTickPreparedForwardHistoryBudget
import ReversibleTickForwardHistoryPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The prepared emitter's full payload uses the preserved actual runtime time and raw length. -/
theorem tickPreparedForwardHistoryTemplate_payload (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hcap : cs (.inl 1)=capacity)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    (ht : 0 < cs (tickTraversalSpare tm 7))
    (hend : cs (tickTraversalSpare tm 1)=firstOutput+cs (tickTraversalSpare tm 7)*(configurationWidth tm capacity*(bound+1)))
    (hbound : cs (tickTraversalSpare tm 1)+bound ≤ wireBound)
    (hlayers : cs (.inl 9)+(cs (tickTraversalSpare tm 7)-1)*tickForestLayerCount tm capacity ≤ layers)
    (hfirst : firstOutput=cs (tickTraversalSpare tm 6)+18*configurationWidth tm capacity) :
    (tickPreparedForwardHistoryTemplate tm bound).bytes cs=
      ((paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound
        (cs (tickTraversalSpare tm 7)) (fun j => cs (tickTraversalSpare tm 6)+17+18*j.val) firstOutput).map
          (rawAssignmentPayload false)).flatten := by
  let initial := (tickHistoryCountTemplate tm).counters cs
  let after := tickPreparedForwardHistoryState tm bound cs
  have hs := tickPreparedForwardHistoryState_budget tm bound wireBound capacity layers firstOutput cs hr hb hcap ht hend hbound hlayers
  have hraw : after (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) :=
    tickPreparedForwardHistoryState_raw_length tm bound cs
  have hremaining : after (tickTraversalSpare tm 3)=cs (tickTraversalSpare tm 7)-1 :=
    tickPreparedForwardHistoryState_remaining tm bound cs
  have hp := tickForwardHistoryTemplate_payload tm bound wireBound capacity layers firstOutput after hs hc hsize
    (by rw [hraw]; exact hfirst)
  rw [hraw,hremaining,Nat.sub_add_cancel (Nat.succ_le_of_lt ht)] at hp
  change ((tickForwardHistoryTemplate tm bound).bytes after++(tickLateWindowTemplate tm bound).bytes initial)++[]=_
  rw [tickLateWindowTemplate_bytes,List.append_nil,List.append_nil]
  exact hp

end ShiReversibleGenerator
