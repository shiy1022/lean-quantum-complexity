import ReversibleTickRetreatIterationTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The real reverse-slice traversal uses a polynomial instruction clock. -/
theorem tickRetreatIterationTemplate_clock (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n firstInput firstOutput (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      TickRetreatIterationBudget tm bound (budget.eval n) (capacity.eval n) (layers.eval n) firstInput firstOutput
        (cs (tickTraversalSpare tm 3)) cs → 0 < capacity.eval n →
      (tickRetreatIterationTemplate tm bound).steps cs ≤ clock.eval n := by
  obtain ⟨unitClock,hunit⟩ := tickRetreatStepTemplate_clock tm (bound+1) bound capacity budget layers hsize
  refine ⟨budget*(unitClock+Polynomial.C 2)+Polynomial.C 1,?_⟩
  intro n firstInput firstOutput cs hs hc
  let p := tickRetreatStepTemplate tm (bound+1) bound
  let remaining := tickTraversalSpare tm 3
  let invariant := fun count (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) Unit) =>
    TickRetreatIterationBudget tm bound (budget.eval n) (capacity.eval n) (layers.eval n) firstInput firstOutput count s.counters
  have h := descendingSteps_bound (templateDescendingBody p remaining) (templateDescendingCost p remaining)
    (unitClock.eval n) invariant ?_ ?_ (cs remaining) (⟨none,cs,[]⟩ : CounterCfg _ Unit) hs
  · rw [descendingTemplateSteps_eq] at h
    change descendingTemplateSteps p remaining (cs remaining) cs ≤ cs remaining*(unitClock.eval n+2)+1 at h
    have hk : cs remaining ≤ budget.eval n := hs.2.2.2.2.1
    have hm := Nat.mul_le_mul_right (unitClock.eval n+2) hk
    change descendingTemplateSteps p remaining (cs remaining) cs ≤ _
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    omega
  · intro k s ht
    have hb := TickRetreatIterationBudget.remaining_update tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
      firstInput firstOutput (k+1) k s.counters ht (by have hk := ht.2.2.2.2.1; omega)
    change p.steps (Function.update s.counters remaining k) ≤ _
    exact hunit n _ hb.2.2.1 hb.1 hb.2.1 hb.2.2.2.1
      (by rw [hb.2.2.1]; exact hc) (by dsimp only [remaining]; have hl := hb.2.2.2.2.2.2.2; omega)
  · intro k s ht
    exact tickRetreatIterationBudget_next tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
      firstInput firstOutput k s.counters ht hc hsize

end ShiReversibleGenerator
