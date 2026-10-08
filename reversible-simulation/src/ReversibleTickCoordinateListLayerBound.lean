import ReversibleTickWindowBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickCoordinateListTemplate_layer_bound (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    (tickCoordinateListTemplate tm kinds inputStride strideBound backward).counters cs (.inl 9) ≤
      cs (.inl 9) + kinds.length * (37 * tickSizeBound tm + 1) := by
  induction kinds generalizing cs with
  | nil => simp [tickCoordinateListTemplate,listProgramTemplate,identityProgramTemplate]
  | cons kind kinds ih =>
    let after := (stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs
    have hai : after (.inl 2) < after (.inl 1) := by
      dsimp only [after]
      rw [stridedTickCoordinateBody_control_frame tm kind inputStride strideBound backward cs 2 (by decide),
        stridedTickCoordinateBody_control_frame tm kind inputStride strideBound backward cs 1 (by decide)]
      exact hi
    have hh := ih after hai
    have hc := stridedTickCoordinateBody_layer_bound tm kind inputStride strideBound backward cs hi
    change (tickCoordinateListTemplate tm kinds inputStride strideBound backward).counters after (.inl 9) ≤ _
    change after (.inl 9) ≤ cs (.inl 9) + (37 * tickSizeBound tm + 1) at hc
    simp only [List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

end ShiReversibleGenerator
