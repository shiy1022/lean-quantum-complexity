import ReversibleInitializationLoopReset

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

theorem constantComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (constantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) ≤
      cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa [constantComponentResult, withCounter, constantComponentStartCfg, constantComponentStart] using
    constantCellTraversal_layer_bound header stackRank symbolCard backward ars (cs (.inl 2)) n (cs (.inl 2)) (constantComponentStartCfg header stackRank symbolCard backward ars cs ys)

theorem constantComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (constantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) bound := by
  have hs := constantComponentStart_budget header stackRank symbolCard backward ars n bound layers cs hn hb ht hbudget hl ys
  have h := constantCellTraversal_final_budget header stackRank symbolCard backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
    (constantComponentStartCfg header stackRank symbolCard backward ars cs ys) haddr hs
  exact h.update (.inr 0) 0 (Nat.zero_le bound)

theorem ascendingConstantComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (ascendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) ≤
      cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa [ascendingConstantComponentResult, withCounter, ascendingConstantComponentStartCfg, ascendingConstantComponentStart] using
    ascendingConstantCellTraversal_layer_bound header stackRank symbolCard backward ars (cs (.inl 2)) n (cs (.inl 2)) (ascendingConstantComponentStartCfg header stackRank symbolCard backward ars cs ys)

theorem ascendingConstantComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = 0) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (ascendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) bound := by
  have hs := ascendingConstantComponentStart_budget header stackRank symbolCard backward ars n bound layers cs hn hi hb ht hbudget hl ys
  have h := ascendingConstantCellTraversal_final_budget header stackRank symbolCard backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
    (ascendingConstantComponentStartCfg header stackRank symbolCard backward ars cs ys) haddr hs
  exact h.update (.inr 11) 0 (Nat.zero_le bound)

end ShiReversibleGenerator
