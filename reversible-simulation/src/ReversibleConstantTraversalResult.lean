import ReversibleConstantTraversalBudget
import ReversibleAscendingConstantBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- A counted traversal retains its maintained invariant at the final zero count. -/
theorem descendingResult_invariant {R L : Type}
    (body : Nat → CounterCfg R L → CounterCfg R L)
    (invariant : Nat → CounterCfg R L → Prop)
    (hnext : ∀ k s, invariant (k + 1) s → invariant k (body k s))
    (count : Nat) (s : CounterCfg R L) (hs : invariant count s) :
    invariant 0 (descendingResult body count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (body k s) (hnext k s hs)

variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

theorem constantCellTraversal_metadata (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))
    (r : WorkspaceRegister) :
    (descendingResult (constantCellBody header stackRank symbolCard backward ars capacity n) count s).counters (.inl r) =
      s.counters (.inl r) := by
  induction count generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [descendingResult, ih]
      simp [constantCellBody, constantSequenceCounters_metadata]

theorem ascendingConstantCellTraversal_metadata (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    (r : WorkspaceRegister) :
    (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s).counters (.inl r) =
      s.counters (.inl r) := by
  induction count generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [descendingResult, ih]
      simp [ascendingConstantCellBody, constantSequenceCounters_metadata]

theorem constantCellTraversal_final_budget (bound layers capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))
    (hb : ∀ ar ∈ ars, n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 ≤ bound)
    (hs : ConstantCellBudgetInvariant header stackRank symbolCard backward ars bound layers capacity n count s) :
    CounterBudget (descendingResult (constantCellBody header stackRank symbolCard backward ars capacity n) count s).counters
      (.inr 10) bound := by
  have h := descendingResult_invariant
    (constantCellBody header stackRank symbolCard backward ars capacity n)
    (ConstantCellBudgetInvariant header stackRank symbolCard backward ars bound layers capacity n)
    (fun k t ht => constantCellBudget_next header stackRank symbolCard backward ars bound layers capacity n k t hb ht)
    count s hs
  exact h.2.1

theorem ascendingConstantCellTraversal_final_budget (bound layers capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    (hb : ∀ ar ∈ ars, n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 ≤ bound)
    (hs : AscendingConstantBudgetInvariant header stackRank symbolCard backward ars bound layers capacity n count s) :
    CounterBudget (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s).counters
      (.inr 10) bound := by
  have h := descendingResult_invariant
    (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n)
    (AscendingConstantBudgetInvariant header stackRank symbolCard backward ars bound layers capacity n)
    (fun k t ht => ascendingConstantBudget_next header stackRank symbolCard backward ars bound layers capacity n k t hb ht)
    count s hs
  exact h.2.1

end ShiReversibleGenerator
