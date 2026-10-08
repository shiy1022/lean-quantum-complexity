import ReversibleTickPreparedForwardHistoryBudget
import ReversibleTickForwardHistoryReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Runtime metadata, not a postulated loop invariant, establishes readiness of the whole forward program. -/
theorem tickPreparedForwardHistoryTemplate_ready (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hcap : cs (.inl 1)=capacity)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    (ht : 0 < cs (tickTraversalSpare tm 7))
    (hend : cs (tickTraversalSpare tm 1)=firstOutput+cs (tickTraversalSpare tm 7)*(configurationWidth tm capacity*(bound+1)))
    (hbound : cs (tickTraversalSpare tm 1)+bound ≤ wireBound)
    (hlayers : cs (.inl 9)+(cs (tickTraversalSpare tm 7)-1)*tickForestLayerCount tm capacity ≤ layers)
    (hin : cs (tickTraversalSpare tm 6)+17+18*configurationWidth tm capacity ≤ wireBound)
    (hout : cs (tickTraversalSpare tm 6)+18*configurationWidth tm capacity+
      configurationWidth tm capacity*(bound+1) ≤ wireBound) :
    (tickPreparedForwardHistoryTemplate tm bound).ready cs := by
  let initial := (tickHistoryCountTemplate tm).counters cs
  let after := tickPreparedForwardHistoryState tm bound cs
  have hi : initial=Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1) :=
    tickHistoryCountTemplate_counters tm cs
  have hs := tickPreparedForwardHistoryState_budget tm bound wireBound capacity layers firstOutput cs hr hb hcap ht hend hbound hlayers
  have hraw : after (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) :=
    tickPreparedForwardHistoryState_raw_length tm bound cs
  change (tickHistoryCountTemplate tm).ready cs ∧
    (tickLateWindowTemplate tm bound).ready initial ∧ (tickForwardHistoryTemplate tm bound).ready after
  refine ⟨hr.2.2.1,?_,?_⟩
  · rw [tickLateWindowTemplate_ready,hi]
    simpa [tickTraversalSpare] using hr.2.2.1
  · exact tickForwardHistoryTemplate_ready tm bound wireBound capacity layers firstOutput after hs hc hsize
      (by rw [hraw]; exact hin) (by rw [hraw]; exact hout)

end ShiReversibleGenerator
