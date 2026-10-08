import ReversibleTickPreparedForwardHistoryTemplate
import ReversibleTickLateWindowHistoryBudget
import ReversibleTickLateWindowMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickPreparedForwardHistoryState (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :=
  (tickLateWindowTemplate tm bound).counters ((tickHistoryCountTemplate tm).counters cs)

theorem tickPreparedForwardHistoryState_remaining (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    tickPreparedForwardHistoryState tm bound cs (tickTraversalSpare tm 3)=cs (tickTraversalSpare tm 7)-1 := by
  rw [tickPreparedForwardHistoryState,tickLateWindowTemplate_remaining,tickHistoryCountTemplate_counters,Function.update_self]

theorem tickPreparedForwardHistoryState_raw_length (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    tickPreparedForwardHistoryState tm bound cs (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) := by
  rw [tickPreparedForwardHistoryState,tickLateWindowTemplate_raw_length,tickHistoryCountTemplate_counters,
    Function.update_of_ne (fun h => (by decide : (6 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h))]

/-- The actual time-count copy and pointer setup establish the real forward emitter's invariant. -/
theorem tickPreparedForwardHistoryState_budget (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hcap : cs (.inl 1)=capacity)
    (ht : 0 < cs (tickTraversalSpare tm 7))
    (hend : cs (tickTraversalSpare tm 1)=firstOutput+cs (tickTraversalSpare tm 7)*(configurationWidth tm capacity*(bound+1)))
    (hbound : cs (tickTraversalSpare tm 1)+bound ≤ wireBound)
    (hlayers : cs (.inl 9)+(cs (tickTraversalSpare tm 7)-1)*tickForestLayerCount tm capacity ≤ layers) :
    TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput
      (tickPreparedForwardHistoryState tm bound cs (tickTraversalSpare tm 3))
      (tickPreparedForwardHistoryState tm bound cs) := by
  let initial := (tickHistoryCountTemplate tm).counters cs
  have hi : initial=Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1) :=
    tickHistoryCountTemplate_counters tm cs
  have hir : fixedGuardedEmitterReady (tickTraversalSupply tm) initial := by
    rw [hi]; simpa [fixedGuardedEmitterReady,tickTraversalSpare] using hr
  have hib : CounterBudget initial (.inl 9) wireBound := by
    rw [hi]
    exact hb.update _ _ ((Nat.sub_le _ _).trans (hb _ (by simp [tickTraversalSpare])))
  have hic : initial (.inl 1)=capacity := by rw [hi]; simpa [tickTraversalSpare] using hcap
  have hi1 : initial (tickTraversalSpare tm 1)=cs (tickTraversalSpare tm 1) := by
    rw [hi,Function.update_of_ne (fun h => (by decide : (1 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h))]
  have hi9 : initial (.inl 9)=cs (.inl 9) := by rw [hi]; simp [tickTraversalSpare]
  rw [tickPreparedForwardHistoryState_remaining]
  exact tickLateWindowTemplate_history_budget tm bound wireBound capacity layers firstOutput
    (cs (tickTraversalSpare tm 7)) initial hir hib hic ht
    ((Nat.sub_le _ _).trans (hb _ (by simp [tickTraversalSpare])))
    (hi1.trans hend) (by rw [hi1]; exact hbound) (by rw [hi9]; exact hlayers)

end ShiReversibleGenerator
