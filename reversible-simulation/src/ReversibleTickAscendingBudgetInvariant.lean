import ReversibleTickSymbolRowStaticBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

def TickAscendingBudgetInvariant (tm : Turing.FinTM2) (inputStride strideBound wireBound layers capacity increment k : Nat)
    {L : Type} (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) L) : Prop :=
  tickAscendingInvariant tm capacity k s ∧
  CounterBudget s.counters (.inl 9) wireBound ∧
  TickWindowBudget tm inputStride strideBound wireBound s.counters ∧
  s.counters (.inl 9) ≤ layers + (capacity-k) * increment

theorem tickSymbolRowAscendingBudget_next (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity k : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).Labels (Fin 3)))
    (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length * (37*tickSizeBound tm+1)) (k+1) s) :
    TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length * (37*tickSizeBound tm+1)) k
      (programDescendingBody (tickSymbolRowAscendingBody tm stack inputStride strideBound backward)
        (tickTraversalSpare tm 0) k s) := by
  have hk := hs.1.2.2
  let cs := Function.update s.counters (tickTraversalSpare tm 0) k
  have hc : capacity ≤ wireBound := by simpa [hs.1.2.1] using hs.2.1 (.inl 1) (by simp)
  have hcs : CounterBudget cs (.inl 9) wireBound := hs.2.1.update _ k (by omega)
  have hw : TickWindowBudget tm inputStride strideBound wireBound cs := by
    simpa [cs,TickWindowBudget,tickTraversalSpare,Fin.ext_iff] using hs.2.2.1
  have hi : cs (.inl 2) < cs (.inl 1) := by
    simp only [cs]
    simp [tickTraversalSpare,hs.1.2.1]
    omega
  have hz : fixedGuardedEmitterReady (tickTraversalSupply tm) cs := by
    simpa [cs,tickTraversalSpare,fixedGuardedEmitterReady] using hs.1.1
  have hb := tickSymbolRowAscendingBody_static_budget tm stack inputStride strideBound backward cs wireBound hcs hw hi hsize
  have hl := tickSymbolRowAscendingBody_layer_bound tm stack inputStride strideBound backward cs hi
  refine ⟨⟨tickSymbolRowAscendingBody_ready_preserved tm stack inputStride strideBound backward cs hz,?_,?_⟩,
    hb.1,hb.2,?_⟩
  · change (tickSymbolRowAscendingBody tm stack inputStride strideBound backward).counters cs (.inl 1) = capacity
    rw [tickSymbolRowAscendingBody_capacity]
    simpa [cs,tickTraversalSpare] using hs.1.2.1
  · change (tickSymbolRowAscendingBody tm stack inputStride strideBound backward).counters cs (.inl 2)+k = capacity
    rw [tickSymbolRowAscendingBody_position]
    simpa [cs,tickTraversalSpare,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hk
  · change (tickSymbolRowAscendingBody tm stack inputStride strideBound backward).counters cs (.inl 9) ≤ _
    have hsub : capacity-k = capacity-(k+1)+1 := by omega
    rw [hsub,Nat.add_mul,Nat.one_mul]
    have hprev := hs.2.2.2
    have he : cs (.inl 9) = s.counters (.inl 9) := by simp [cs,tickTraversalSpare]
    rw [he] at hl
    omega

end ShiReversibleGenerator
