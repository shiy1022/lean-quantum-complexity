import ReversibleStridedTickDescendingTraversal
import ReversibleTickCoordinateListLayerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

def TickDescendingBudgetInvariant (tm : Turing.FinTM2) (inputStride strideBound wireBound layers capacity increment k : Nat)
    {L : Type} (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) L) : Prop :=
  tickDescendingInvariant tm capacity k s ∧
  CounterBudget s.counters (.inl 9) wireBound ∧
  TickWindowBudget tm inputStride strideBound wireBound s.counters ∧
  s.counters (.inl 9) ≤ layers + (capacity - k) * increment

/-- Fixed windows and a separate linear layer budget survive the actual descending body. -/
theorem tickCoordinateListDescendingBudget_next (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity k : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3)))
    (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length * (37 * tickSizeBound tm + 1)) (k+1) s) :
    TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length * (37 * tickSizeBound tm + 1)) k
      (programDescendingBody (tickCoordinateListTemplate tm kinds inputStride strideBound backward) (.inl 2) k s) := by
  have hk := hs.1.2.2
  let cs := Function.update s.counters (Sum.inl 2 : FixedLeafRegister (tickTraversalSupply tm)) k
  have hc : capacity ≤ wireBound := by
    simpa [hs.1.2.1] using hs.2.1 (.inl 1) (by simp)
  have hcs : CounterBudget cs (.inl 9) wireBound := hs.2.1.update (.inl 2) k (by omega)
  have hwin := TickWindowBudget.position_update tm inputStride strideBound wireBound s.counters k hs.2.2.1
  have hi : cs (.inl 2) < cs (.inl 1) := by simp only [cs,Function.update_self]; simpa [cs,hs.1.2.1] using hs.1.2.2
  have hz : fixedGuardedEmitterReady (tickTraversalSupply tm) cs := by
    simpa [cs,fixedGuardedEmitterReady] using hs.1.1
  have hb := tickCoordinateListTemplate_static_budget tm kinds inputStride strideBound backward cs wireBound hcs hwin hi hsize
  have hl := tickCoordinateListTemplate_layer_bound tm kinds inputStride strideBound backward cs hi
  refine ⟨⟨tickCoordinateListTemplate_ready_preserved tm kinds inputStride strideBound backward cs hz, ?_, by omega⟩,
    hb.1,hb.2,?_⟩
  · change (tickCoordinateListTemplate tm kinds inputStride strideBound backward).counters cs (.inl 1) = capacity
    rw [tickCoordinateListTemplate_control_frame tm kinds inputStride strideBound backward cs 1 (by decide)]
    simpa [cs] using hs.1.2.1
  · change (tickCoordinateListTemplate tm kinds inputStride strideBound backward).counters cs (.inl 9) ≤ _
    have hsub : capacity-k = capacity-(k+1)+1 := by omega
    rw [hsub,Nat.add_mul,Nat.one_mul]
    have hprev := hs.2.2.2
    have he : cs (.inl 9) = s.counters (.inl 9) := by simp [cs]
    rw [he] at hl
    omega

end ShiReversibleGenerator
