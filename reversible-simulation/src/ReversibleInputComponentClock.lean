import ReversibleInputComponentFrames
import ReversibleAscendingSymbolBudget
import ReversibleSymbolTraversalBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

theorem inputComponentStart_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers) (ys : List Bool) :
    SymbolCellBudgetInvariant header stackRank symbolCard tm e backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
      (inputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys) := by
  refine ⟨inputComponentStart_invariant header stackRank symbolCard tm e backward ars cs n hn hb ht none ys, ?_, ?_⟩
  · exact hbudget.update (.inr 0) (cs (.inl 2)) (hbudget (.inl 2) (by decide))
  · simpa [inputComponentStartCfg, constantComponentStart] using hl

/-- The actual component clock remains polynomial when its input counters are intermediate states. -/
theorem inputComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n →
      cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      inputComponentSteps header stackRank symbolCard tm e backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := symbolCellTraversal_polynomial_bound header stackRank symbolCard tm e backward ars capacity budget layers haddr
  refine ⟨Polynomial.C 7 * capacity + Polynomial.C 2 + clock, ?_⟩
  intro n cs ys hn hcap hb ht hbudget hl
  have hs := inputComponentStart_budget header stackRank symbolCard tm e backward ars n (budget.eval n) (layers.eval n) cs hn hb ht hbudget hl ys
  rw [hcap] at hs
  have h := hc n (capacity.eval n) (inputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys) hs
  simpa only [inputComponentSteps, hcap, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add_left h (7 * capacity.eval n + 2)

theorem ascendingInputComponentStart_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = 0) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers) (ys : List Bool) :
    AscendingSymbolBudgetInvariant header stackRank symbolCard tm e backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
      (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys) := by
  refine ⟨ascendingInputComponentStart_invariant header stackRank symbolCard tm e backward ars cs n hn hi hb ht none ys, ?_, ?_⟩
  · exact hbudget.update (.inr 11) (cs (.inl 2)) (hbudget (.inl 2) (by decide))
  · simpa [ascendingInputComponentStartCfg, ascendingConstantComponentStart] using hl

/-- The actual component clock remains polynomial when its input counters are intermediate states. -/
theorem ascendingInputComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n →
      cs (.inr 0) = 0 → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      ascendingInputComponentSteps header stackRank symbolCard tm e backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := ascendingSymbolTraversal_polynomial_bound header stackRank symbolCard tm e backward ars capacity budget layers haddr
  refine ⟨Polynomial.C 7 * capacity + Polynomial.C 2 + clock, ?_⟩
  intro n cs ys hn hcap hi hb ht hbudget hl
  have hs := ascendingInputComponentStart_budget header stackRank symbolCard tm e backward ars n (budget.eval n) (layers.eval n) cs hn hi hb ht hbudget hl ys
  rw [hcap] at hs
  have h := hc n (capacity.eval n) (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys) hs
  simpa only [ascendingInputComponentSteps, hcap, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add_left h (7 * capacity.eval n + 2)

end ShiReversibleGenerator
