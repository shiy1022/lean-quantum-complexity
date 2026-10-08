import ReversibleGuardedTreeCounterBudget
import ReversibleStridedTickAscendingBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem stridedTickCoordinateBody_counter_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ q, cs q ≤ bound.eval n) → ∀ q,
      (stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs q ≤ budget.eval n := by
  obtain ⟨budget, hb⟩ := stridedSharedFixedGuardedEmitter_counter_bound (tickTraversalSupply tm)
    (tickTreeForKind tm kind) inputStride backward
    (bound + tickPreparedOutputBudget tm kind strideBound bound + Polynomial.C strideBound)
  refine ⟨budget, ?_⟩
  intro n cs hc q
  exact hb n (tickOutputPreparationCounters tm kind strideBound cs)
    (tickOutputPreparationCounters_bound tm kind strideBound bound n cs hc) q

theorem stridedTickAscendingBody_counter_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ q, cs q ≤ bound.eval n) → ∀ q,
      (stridedTickAscendingBody tm kind inputStride strideBound backward).counters cs q ≤ budget.eval n := by
  obtain ⟨budget, hb⟩ := stridedTickCoordinateBody_counter_bound tm kind inputStride strideBound backward bound
  refine ⟨budget + 1, ?_⟩
  intro n cs hc q
  change Function.update ((stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs)
    (.inl 2) ((stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs (.inl 2) + 1) q ≤ _
  by_cases hq : q = .inl 2
  · subst q
    simpa only [Function.update_self, Polynomial.eval_add, Polynomial.eval_one] using Nat.add_le_add_right (hb n cs hc (.inl 2)) 1
  · simpa only [Function.update_of_ne hq, Polynomial.eval_add, Polynomial.eval_one] using
      (hb n cs hc q).trans (Nat.le_add_right _ _)

end ShiReversibleGenerator
