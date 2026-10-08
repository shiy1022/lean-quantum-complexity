import ReversibleStridedPrivateCounterBound
import ReversibleCounterBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- One complete coordinate preserves the static counter budget except for its layer count. -/
theorem stridedTickCoordinateBody_static_budget (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (hbudget : CounterBudget cs (.inl 9) wireBound)
    (hi : cs (.inl 2) < cs (.inl 1))
    (hin : cs (.inl 0) + inputStride * configurationWidth tm (cs (.inl 1)) ≤ wireBound)
    (hout : tickPreparedOutputAddress tm kind strideBound cs + strideBound ≤ wireBound)
    (hsize : tickSizeBound tm ≤ strideBound) :
    CounterBudget ((stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs)
      (.inl 9) wireBound := by
  have hf := stridedTickCoordinateBody_fields_bound tm kind inputStride strideBound backward cs wireBound
    hi hin hout hsize
  intro r hr
  cases r with
  | inr j =>
    exact le_trans (stridedTickCoordinateBody_private_le tm kind inputStride strideBound backward cs j)
      (hbudget _ (by simp))
  | inl q =>
    by_cases h6 : q = 6
    · subst q; exact hf.1
    by_cases h7 : q = 7
    · subst q; exact hf.2.1
    by_cases h8 : q = 8
    · subst q; exact hf.2.2
    have h9 : q ≠ 9 := by simpa using hr
    by_cases h12 : q = 12
    · subst q
      change (stridedSharedFixedGuardedEmitter (tickTraversalSupply tm) (tickTreeForKind tm kind)
        inputStride backward).counters (tickOutputPreparationCounters tm kind strideBound cs) (.inl 12) ≤ wireBound
      rw [stridedSharedFixedGuardedEmitter_control_frame _ _ _ _ _ 12 (by decide)]
      simpa [tickOutputPreparationCounters] using le_trans (Nat.le_add_right
        (tickPreparedOutputAddress tm kind strideBound cs) strideBound) hout
    by_cases h13 : q = 13
    · subst q
      change (stridedSharedFixedGuardedEmitter (tickTraversalSupply tm) (tickTreeForKind tm kind)
        inputStride backward).counters (tickOutputPreparationCounters tm kind strideBound cs) (.inl 13) ≤ wireBound
      rw [stridedSharedFixedGuardedEmitter_control_frame _ _ _ _ _ 13 (by decide)]
      simpa [tickOutputPreparationCounters] using hout
    rw [stridedTickCoordinateBody_control_frame tm kind inputStride strideBound backward cs q
      ⟨h6,h7,h8,h9,h12,h13⟩]
    exact hbudget _ hr

end ShiReversibleGenerator
