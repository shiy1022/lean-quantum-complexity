import ReversibleTickStaticCounterBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The emitted layer count grows by a machine-dependent constant per coordinate. -/
theorem stridedTickCoordinateBody_layer_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    (stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs (.inl 9) ≤
      cs (.inl 9) + (37 * tickSizeBound tm + 1) := by
  rw [stridedTickCoordinateBody_count tm kind inputStride strideBound backward cs hi]
  have h := formulaElementaryLayers_bound (boundedTickFormulaForKind tm (cs (.inl 1)) ⟨cs (.inl 2),hi⟩ kind)
  have hs := boundedTickFormulaForKind_size tm (cs (.inl 1)) ⟨cs (.inl 2),hi⟩ kind
  have hm := Nat.mul_le_mul_left 37 hs
  omega

end ShiReversibleGenerator
