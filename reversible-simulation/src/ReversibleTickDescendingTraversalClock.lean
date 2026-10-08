import ReversibleTickDescendingBudgetInvariant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual variable-length coordinate-list loop has a polynomial instruction clock. -/
theorem tickCoordinateListDescendingTraversal_polynomial (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
        ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3))),
      TickDescendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
        (kinds.length * (37 * tickSizeBound tm + 1)) count s →
      descendingSteps (programDescendingBody (tickCoordinateListTemplate tm kinds inputStride strideBound backward) (.inl 2))
        (programDescendingCost (tickCoordinateListTemplate tm kinds inputStride strideBound backward) (.inl 2)) count s ≤ clock.eval n := by
  let increment := kinds.length * (37 * tickSizeBound tm + 1)
  let totalBudget := budget + layers + capacity * Polynomial.C increment
  obtain ⟨unitClock,hunit⟩ := (tickCoordinateListTemplate_polynomial_certificate tm kinds inputStride strideBound backward totalBudget).2
  refine ⟨capacity * (unitClock + Polynomial.C 2) + Polynomial.C 1,?_⟩
  intro n count s hs
  let p := tickCoordinateListTemplate tm kinds inputStride strideBound backward
  let invariant := fun k (t : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) (p.Labels (Fin 3))) =>
    TickDescendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n) increment k t
  have hcost : ∀ k t, invariant (k+1) t → programDescendingCost p (.inl 2) k t ≤ unitClock.eval n := by
    intro k t ht
    let cs := Function.update t.counters (Sum.inl 2 : FixedLeafRegister (tickTraversalSupply tm)) k
    have hc : capacity.eval n ≤ budget.eval n := by
      simpa [ht.1.2.1] using ht.2.1 (.inl 1) (by simp)
    have hb : CounterBudget cs (.inl 9) (budget.eval n) := ht.2.1.update (.inl 2) k (by have hk := ht.1.2.2; omega)
    apply hunit n cs
    · intro q
      simp only [totalBudget,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
      by_cases hq : q = .inl 9
      · subst q
        have he : cs (.inl 9) = t.counters (.inl 9) := by simp [cs]
        have hl := ht.2.2.2
        have hm := Nat.mul_le_mul_right increment (Nat.sub_le (capacity.eval n) (k+1))
        rw [he]
        omega
      · have hh := hb q hq
        omega
    · apply tickCoordinateListTemplate_ready
      simpa [cs,fixedGuardedEmitterReady] using ht.1.1
  have hrun := descendingSteps_bound (programDescendingBody p (.inl 2))
    (programDescendingCost p (.inl 2)) (unitClock.eval n) invariant hcost
    (fun k t ht => tickCoordinateListDescendingBudget_next tm kinds inputStride strideBound backward
      (budget.eval n) (layers.eval n) (capacity.eval n) k t hsize ht) count s hs
  have hk := hs.1.2.2
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  exact hrun.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1)

end ShiReversibleGenerator
