import ReversibleLocatedConstantBudget
import ReversibleConstantCellLayerBound

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat) (backward : Bool)

theorem constantSequence_counterBudget (ars : List (Bool × Nat))
    (cs : InitializationRegister → Nat) (bound : Nat) (h : CounterBudget cs (.inr 10) bound)
    (hi : cs (.inr 0) + 1 ≤ bound)
    (hb : ∀ ar ∈ ars, cs (.inl 0) +
      18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2) + 18 ≤ bound) :
    CounterBudget (constantSequenceCounters header stackRank symbolCard backward ars cs) (.inr 10) bound := by
  induction ars generalizing cs with
  | nil => exact h
  | cons ar ars ih =>
      apply ih
      · exact locatedConstant_counterBudget header stackRank symbolCard ar.2 ar.1 backward cs bound h hi
          (hb ar (by simp))
      · simpa [locatedConstant_preserves_index] using hi
      · intro br hbr
        simpa [locatedConstant_preserves_metadata, locatedConstant_preserves_index] using hb br (by simp [hbr])

/-- A fixed finite symbol list has a polynomial clock under the maintained register budgets. -/
theorem constantSequence_budget_polynomial_bound (ars : List (Bool × Nat))
    (budget layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat),
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      cs (.inr 0) + 1 ≤ budget.eval n →
      (∀ ar ∈ ars, cs (.inl 0) +
        18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2) + 18 ≤ budget.eval n) →
      constantSequenceSteps header stackRank symbolCard backward ars cs ≤ clock.eval n := by
  induction ars generalizing layers with
  | nil => exact ⟨0, by intros; simp [constantSequenceSteps]⟩
  | cons ar ars ih =>
      let sizes : InitializationRegister → Polynomial Nat := fun r => if r = .inr 10 then layers else budget
      obtain ⟨first, hf⟩ := locatedConstant_polynomial_bound header stackRank symbolCard ar.2 ar.1 backward sizes
      obtain ⟨rest, hr⟩ := ih (layers + Polynomial.C 630)
      refine ⟨first + rest, ?_⟩
      intro n cs h hl hi hb
      have hfirst := hf n cs (by
        intro r
        by_cases he : r = (Sum.inr 10 : InitializationRegister)
        · subst r; simpa [sizes] using hl
        · simpa [sizes, he] using h r he)
      have hnext := locatedConstant_counterBudget header stackRank symbolCard ar.2 ar.1 backward cs
        (budget.eval n) h hi (hb ar (by simp))
      have hlayer : locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs (.inr 10) ≤
          (layers + Polynomial.C 630).eval n := by
        have hx := locatedConstant_layer_bound header stackRank symbolCard ar.2 ar.1 backward cs
        simp only [Polynomial.eval_add, Polynomial.eval_C]
        omega
      have hrest := hr n (locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs)
        hnext hlayer (by simpa [locatedConstant_preserves_index] using hi)
        (by intro br hbr; simpa [locatedConstant_preserves_metadata, locatedConstant_preserves_index] using hb br (by simp [hbr]))
      simpa only [constantSequenceSteps, Polynomial.eval_add] using Nat.add_le_add hfirst hrest

end ShiReversibleGenerator
