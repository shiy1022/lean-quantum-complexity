import ReversibleTickCoordinateLayerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Every prepared target and its padding fit in the whole output forest window. -/
theorem tickPreparedOutputAddress_window_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (strideBound : Nat) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hi : cs (.inl 2) < cs (.inl 1)) :
    tickPreparedOutputAddress tm kind strideBound cs + strideBound ≤
      cs (tickTraversalSpare tm 2) + configurationWidth tm (cs (.inl 1)) * (strideBound + 1) := by
  rw [tickPreparedOutputAddress_coordinate tm kind strideBound cs hi]
  let j := configurationBitEquiv tm (cs (.inl 1)) (tickKindBit tm (cs (.inl 1)) ⟨cs (.inl 2), hi⟩ kind)
  have hj : j.val + 1 ≤ configurationWidth tm (cs (.inl 1)) := j.isLt
  have hm := Nat.mul_le_mul_right (strideBound + 1) hj
  simp only [Nat.add_mul, Nat.one_mul] at hm
  change cs (tickTraversalSpare tm 2) + j.val * (strideBound + 1) + strideBound ≤ _
  omega

/-- The whole-window hypotheses hold for every valid position and selected coordinate. -/
theorem stridedTickCoordinateBody_window_budget (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (hbudget : CounterBudget cs (.inl 9) wireBound)
    (hi : cs (.inl 2) < cs (.inl 1))
    (hin : cs (.inl 0) + inputStride * configurationWidth tm (cs (.inl 1)) ≤ wireBound)
    (hout : cs (tickTraversalSpare tm 2) + configurationWidth tm (cs (.inl 1)) * (strideBound + 1) ≤ wireBound)
    (hsize : tickSizeBound tm ≤ strideBound) :
    CounterBudget ((stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs)
      (.inl 9) wireBound :=
  stridedTickCoordinateBody_static_budget tm kind inputStride strideBound backward cs wireBound hbudget hi hin
    (le_trans (tickPreparedOutputAddress_window_bound tm kind strideBound cs hi) hout) hsize

end ShiReversibleGenerator
