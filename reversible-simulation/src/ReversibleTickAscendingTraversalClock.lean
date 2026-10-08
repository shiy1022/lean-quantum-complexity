import ReversibleTickAscendingBudgetInvariant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The increasing position traversal used for reversed forest emission has an actual polynomial clock. -/
theorem tickSymbolRowAscendingTraversal_polynomial (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
        ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).Labels (Fin 3))),
      TickAscendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
        ((tickSymbolRowKinds tm stack).length * (37*tickSizeBound tm+1)) count s →
      descendingSteps (programDescendingBody (tickSymbolRowAscendingBody tm stack inputStride strideBound backward)
          (tickTraversalSpare tm 0))
        (programDescendingCost (tickSymbolRowAscendingBody tm stack inputStride strideBound backward)
          (tickTraversalSpare tm 0)) count s ≤ clock.eval n := by
  let increment := (tickSymbolRowKinds tm stack).length * (37*tickSizeBound tm+1)
  let totalBudget := budget+layers+capacity*Polynomial.C increment
  obtain ⟨unitClock,hunit⟩ := tickSymbolRowAscendingBody_polynomial tm stack inputStride strideBound backward totalBudget
  refine ⟨capacity*(unitClock+Polynomial.C 2)+Polynomial.C 1,?_⟩
  intro n count s hs
  let p := tickSymbolRowAscendingBody tm stack inputStride strideBound backward
  let remaining := tickTraversalSpare tm 0
  let invariant := fun k (t : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) (p.Labels (Fin 3))) =>
    TickAscendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n) increment k t
  have hcost : ∀ k t, invariant (k+1) t → programDescendingCost p remaining k t ≤ unitClock.eval n := by
    intro k t ht
    have hk := ht.1.2.2
    let cs := Function.update t.counters remaining k
    have hc : capacity.eval n ≤ budget.eval n := by simpa [ht.1.2.1] using ht.2.1 (.inl 1) (by simp)
    have hb : CounterBudget cs (.inl 9) (budget.eval n) := ht.2.1.update remaining k (by omega)
    apply hunit n cs
    · intro q
      simp only [totalBudget,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
      by_cases hq : q = .inl 9
      · subst q
        have he : cs (.inl 9) = t.counters (.inl 9) := by simp [cs,remaining,tickTraversalSpare]
        have hl := ht.2.2.2
        have hm := Nat.mul_le_mul_right increment (Nat.sub_le (capacity.eval n) (k+1))
        rw [he]
        omega
      · have hh := hb q hq
        omega
    · apply tickSymbolRowAscendingBody_ready
      simpa [cs,remaining,tickTraversalSpare,fixedGuardedEmitterReady] using ht.1.1
  have hrun := descendingSteps_bound (programDescendingBody p remaining) (programDescendingCost p remaining)
    (unitClock.eval n) invariant hcost
    (fun k t ht => tickSymbolRowAscendingBudget_next tm stack inputStride strideBound backward
      (budget.eval n) (layers.eval n) (capacity.eval n) k t hsize ht) count s hs
  have hk := hs.1.2.2
  have hcount : count ≤ capacity.eval n := by omega
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  exact hrun.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hcount) 1)

end ShiReversibleGenerator
