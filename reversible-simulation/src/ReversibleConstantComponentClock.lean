import ReversibleConstantComponentFrames

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

theorem constantComponentStart_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers) (ys : List Bool) :
    ConstantCellBudgetInvariant header stackRank symbolCard backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
      (constantComponentStartCfg header stackRank symbolCard backward ars cs ys) := by
  refine ⟨constantComponentStart_invariant header stackRank symbolCard backward ars cs n hn hb ht none ys, ?_, ?_⟩
  · exact hbudget.update (.inr 0) (cs (.inl 2)) (hbudget (.inl 2) (by decide))
  · simpa [constantComponentStartCfg, constantComponentStart] using hl

/-- The actual component clock remains polynomial when its input counters are intermediate states. -/
theorem constantComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n →
      cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      constantComponentSteps header stackRank symbolCard backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := constantCellTraversal_polynomial_bound header stackRank symbolCard backward ars capacity budget layers haddr
  refine ⟨Polynomial.C 7 * capacity + Polynomial.C 2 + clock, ?_⟩
  intro n cs ys hn hcap hb ht hbudget hl
  have hs := constantComponentStart_budget header stackRank symbolCard backward ars n (budget.eval n) (layers.eval n) cs hn hb ht hbudget hl ys
  rw [hcap] at hs
  have h := hc n (capacity.eval n) (constantComponentStartCfg header stackRank symbolCard backward ars cs ys) hs
  simpa only [constantComponentSteps, hcap, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add_left h (7 * capacity.eval n + 2)

theorem ascendingConstantComponentStart_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = 0) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers) (ys : List Bool) :
    AscendingConstantBudgetInvariant header stackRank symbolCard backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
      (ascendingConstantComponentStartCfg header stackRank symbolCard backward ars cs ys) := by
  refine ⟨ascendingConstantComponentStart_invariant header stackRank symbolCard backward ars cs n hn hi hb ht none ys, ?_, ?_⟩
  · exact hbudget.update (.inr 11) (cs (.inl 2)) (hbudget (.inl 2) (by decide))
  · simpa [ascendingConstantComponentStartCfg, ascendingConstantComponentStart] using hl

/-- The actual component clock remains polynomial when its input counters are intermediate states. -/
theorem ascendingConstantComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n →
      cs (.inr 0) = 0 → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      ascendingConstantComponentSteps header stackRank symbolCard backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := ascendingConstantTraversal_polynomial_bound header stackRank symbolCard backward ars capacity budget layers haddr
  refine ⟨Polynomial.C 7 * capacity + Polynomial.C 2 + clock, ?_⟩
  intro n cs ys hn hcap hi hb ht hbudget hl
  have hs := ascendingConstantComponentStart_budget header stackRank symbolCard backward ars n (budget.eval n) (layers.eval n) cs hn hi hb ht hbudget hl ys
  rw [hcap] at hs
  have h := hc n (capacity.eval n) (ascendingConstantComponentStartCfg header stackRank symbolCard backward ars cs ys) hs
  simpa only [ascendingConstantComponentSteps, hcap, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add_left h (7 * capacity.eval n + 2)

end ShiReversibleGenerator
