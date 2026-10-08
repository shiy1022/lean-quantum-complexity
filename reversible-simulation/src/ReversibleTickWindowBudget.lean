import ReversibleTickOutputWindowBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

def TickWindowBudget (tm : Turing.FinTM2) (inputStride strideBound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) : Prop :=
  cs (.inl 0) + inputStride * configurationWidth tm (cs (.inl 1)) ≤ wireBound ∧
  cs (tickTraversalSpare tm 2) + configurationWidth tm (cs (.inl 1)) * (strideBound + 1) ≤ wireBound

theorem TickWindowBudget.position_update (tm : Turing.FinTM2) (inputStride strideBound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (k : Nat)
    (h : TickWindowBudget tm inputStride strideBound wireBound cs) :
    TickWindowBudget tm inputStride strideBound wireBound (Function.update cs (.inl 2) k) := by
  simpa [TickWindowBudget,tickTraversalSpare] using h

theorem stridedTickCoordinateBody_windows_preserved (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (h : TickWindowBudget tm inputStride strideBound wireBound cs) :
    TickWindowBudget tm inputStride strideBound wireBound
      ((stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs) := by
  unfold TickWindowBudget
  rw [stridedTickCoordinateBody_control_frame tm kind inputStride strideBound backward cs 0 (by decide),
    stridedTickCoordinateBody_control_frame tm kind inputStride strideBound backward cs 1 (by decide),
    stridedTickCoordinateBody_spare_frame tm kind inputStride strideBound backward cs 2]
  exact h

/-- A fixed coordinate list preserves one common window and counter budget. -/
theorem tickCoordinateListTemplate_static_budget (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hi : cs (.inl 2) < cs (.inl 1)) (hs : tickSizeBound tm ≤ strideBound) :
    CounterBudget ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).counters cs) (.inl 9) wireBound ∧
    TickWindowBudget tm inputStride strideBound wireBound
      ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).counters cs) := by
  induction kinds generalizing cs with
  | nil => exact ⟨hb,hw⟩
  | cons kind kinds ih =>
    let after := (stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs
    have hab := stridedTickCoordinateBody_window_budget tm kind inputStride strideBound backward cs wireBound
      hb hi hw.1 hw.2 hs
    have haw := stridedTickCoordinateBody_windows_preserved tm kind inputStride strideBound backward cs wireBound hw
    have hai : after (.inl 2) < after (.inl 1) := by
      dsimp only [after]
      rw [stridedTickCoordinateBody_control_frame tm kind inputStride strideBound backward cs 2 (by decide),
        stridedTickCoordinateBody_control_frame tm kind inputStride strideBound backward cs 1 (by decide)]
      exact hi
    exact ih after hab haw hai

end ShiReversibleGenerator
