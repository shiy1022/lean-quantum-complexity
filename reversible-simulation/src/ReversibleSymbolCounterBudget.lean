import ReversibleLocatedCounterBudget
import ReversibleInitializationLayerBound

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)

theorem symbolSequence_counterBudget (ars : List (Option (MachineSymbol tm) × Nat))
    (cs : InitializationRegister → Nat) (bound : Nat) (h : CounterBudget cs (.inr 10) bound)
    (hi : cs (.inr 0) + 1 ≤ bound)
    (hb : ∀ ar ∈ ars, cs (.inl 0) +
      18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2) + 18 ≤ bound) :
    CounterBudget (symbolSequenceCounters header stackRank symbolCard tm e backward ars cs) (.inr 10) bound := by
  induction ars generalizing cs with
  | nil => exact h
  | cons ar ars ih =>
      apply ih
      · exact locatedInitialization_counterBudget header stackRank symbolCard ar.2 tm e ar.1 backward cs bound h hi
          (hb ar (by simp))
      · simpa [locatedInitialization_preserves_index] using hi
      · intro br hbr
        simpa [locatedInitialization_preserves_metadata, locatedInitialization_preserves_index] using hb br (by simp [hbr])

/-- A fixed finite symbol list has a polynomial clock under the maintained register budgets. -/
theorem symbolSequence_polynomial_bound (ars : List (Option (MachineSymbol tm) × Nat))
    (budget layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat),
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      cs (.inr 0) + 1 ≤ budget.eval n →
      (∀ ar ∈ ars, cs (.inl 0) +
        18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2) + 18 ≤ budget.eval n) →
      symbolSequenceSteps header stackRank symbolCard tm e backward ars cs ≤ clock.eval n := by
  induction ars generalizing layers with
  | nil => exact ⟨0, by intros; simp [symbolSequenceSteps]⟩
  | cons ar ars ih =>
      let sizes : InitializationRegister → Polynomial Nat := fun r => if r = .inr 10 then layers else budget
      obtain ⟨first, hf⟩ := locatedInitialization_polynomial_bound header stackRank symbolCard ar.2 tm e ar.1 backward sizes
      obtain ⟨rest, hr⟩ := ih (layers + Polynomial.C 630)
      refine ⟨first + rest, ?_⟩
      intro n cs h hl hi hb
      have hfirst := hf n cs (by
        intro r
        by_cases he : r = (Sum.inr 10 : InitializationRegister)
        · subst r; simpa [sizes] using hl
        · simpa [sizes, he] using h r he)
      have hnext := locatedInitialization_counterBudget header stackRank symbolCard ar.2 tm e ar.1 backward cs
        (budget.eval n) h hi (hb ar (by simp))
      have hlayer : locatedInitializationCounters header stackRank symbolCard ar.2 tm e ar.1 backward cs (.inr 10) ≤
          (layers + Polynomial.C 630).eval n := by
        have hx := locatedInitialization_layer_bound header stackRank symbolCard ar.2 tm e ar.1 backward cs
        simp only [Polynomial.eval_add, Polynomial.eval_C]
        omega
      have hrest := hr n (locatedInitializationCounters header stackRank symbolCard ar.2 tm e ar.1 backward cs)
        hnext hlayer (by simpa [locatedInitialization_preserves_index] using hi)
        (by intro br hbr; simpa [locatedInitialization_preserves_metadata, locatedInitialization_preserves_index] using hb br (by simp [hbr]))
      simpa only [symbolSequenceSteps, Polynomial.eval_add] using Nat.add_le_add hfirst hrest

end ShiReversibleGenerator
