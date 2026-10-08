import ReversibleStridedSelectedFieldBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Preparing one output coordinate and printing its selected formula resets address fields
within the same static input/output window budget, independently of the layer count. -/
theorem stridedTickCoordinateBody_fields_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (hi : cs (.inl 2) < cs (.inl 1))
    (hin : cs (.inl 0) + inputStride * configurationWidth tm (cs (.inl 1)) ≤ wireBound)
    (hout : tickPreparedOutputAddress tm kind strideBound cs + strideBound ≤ wireBound)
    (hsize : tickSizeBound tm ≤ strideBound) :
    let final := (stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs
    final (.inl 6) ≤ wireBound ∧ final (.inl 7) ≤ wireBound ∧ final (.inl 8) ≤ wireBound := by
  let after := tickOutputPreparationCounters tm kind strideBound cs
  change let final := (stridedTickTraversalEmitter tm kind inputStride backward).counters after
         final (.inl 6) ≤ wireBound ∧ final (.inl 7) ≤ wireBound ∧ final (.inl 8) ≤ wireBound
  apply stridedTickTraversalEmitter_fields_bound
  · simpa [after, tickOutputPreparationCounters] using hi
  · simpa [after, tickOutputPreparationCounters] using hin
  · dsimp only [after]
    simp only [tickOutputPreparationCounters, Function.update_apply, Sum.inl.injEq,
      reduceCtorEq, Fin.reduceEq, if_true, if_false]
    exact le_trans (Nat.add_le_add_left hsize _) hout
  · simpa [after, tickOutputPreparationCounters] using hout

end ShiReversibleGenerator
