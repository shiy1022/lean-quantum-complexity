import ReversibleInitializerSequence

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Resource evidence is separate from finite control and must be supplied by actual component proofs. -/
structure InitializationResources (c : InitializationComponent) (capacity budget : Polynomial Nat) where
  growth : Nat
  layers : ∀ n cs ys, (c.counters n cs ys) (.inr 10) ≤ cs (.inr 10) + cs (.inl 2) * growth
  preserved : ∀ n cs ys, cs (.inl 0) = n → cs (.inl 2) = capacity.eval n →
    cs (.inl 6) = 0 → cs (.inl 5) = 0 → CounterBudget cs (.inr 10) (budget.eval n) →
    CounterBudget (c.counters n cs ys) (.inr 10) (budget.eval n)
  clock : ∀ layers : Polynomial Nat, ∃ clock : Polynomial Nat, ∀ n cs ys,
    cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
    CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
    c.steps n cs ys ≤ clock.eval n

/-- Fixed finite sequencing sums real clocks and connecting branches; layer bounds grow only additively. -/
theorem initializerSequence_polynomial_bound (components : List InitializationComponent)
    (capacity budget : Polynomial Nat) :
    (∀ c ∈ components, InitializationResources c capacity budget) →
    ∀ layers : Polynomial Nat, ∃ clock : Polynomial Nat, ∀ n cs ys,
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      initializerSequenceSteps components n cs ys ≤ clock.eval n := by
  induction components with
  | nil =>
      intro resources layers
      refine ⟨0, ?_⟩
      intro n cs ys hn hcap hb ht hbudget hl
      simp [initializerSequenceSteps]
  | cons c rest ih =>
      intro resources layers
      let rc := resources c (by simp)
      obtain ⟨p, hp⟩ := rc.clock layers
      obtain ⟨q, hq⟩ := ih (fun d hd => resources d (by simp [hd]))
        (layers + capacity * Polynomial.C rc.growth)
      refine ⟨p + Polynomial.C 1 + q, ?_⟩
      intro n cs ys hn hcap hb ht hbudget hl
      have hfirst := hp n cs ys hn hcap hb ht hbudget hl
      have hbudget' := rc.preserved n cs ys hn hcap hb ht hbudget
      have hl' : (c.counters n cs ys) (.inr 10) ≤
          (layers + capacity * Polynomial.C rc.growth).eval n := by
        have hg := rc.layers n cs ys
        rw [hcap] at hg
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        exact hg.trans (Nat.add_le_add_right hl _)
      have hrest := hq n (c.counters n cs ys) (c.output n cs ys)
        (by simpa only [c.metadata] using hn)
        (by simpa only [c.metadata] using hcap)
        (by simpa only [c.metadata] using hb)
        (by simpa only [c.metadata] using ht) hbudget' hl'
      simpa only [initializerSequenceSteps, Polynomial.eval_add, Polynomial.eval_C] using
        Nat.add_le_add (Nat.add_le_add_right hfirst 1) hrest

end ShiReversibleGenerator
