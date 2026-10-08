import ReversibleCoordinateBindingProgramTemplate
import ReversibleStridedCoordinateBindingBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- A concrete finite binder has both an exact polynomial clock and a polynomial bound on all exit counters. -/
theorem coordinateBindingProgramTemplate_resources (tm : Turing.FinTM2)
    (r : CoordinateBindingRegisters R) (stride : Nat) (coordinate : TickSymbolicCoordinate tm)
    (hv : r.Valid) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q,cs q ≤ bound.eval n) →
      (∀ q,(coordinateBindingProgramTemplate tm r stride coordinate).counters cs q ≤ budget.eval n) ∧
      (coordinateBindingProgramTemplate tm r stride coordinate).steps cs ≤ clock.eval n := by
  obtain ⟨addressBudget,ha⟩ := stridedTickCoordinateAddress_polynomial tm r stride coordinate bound
  obtain ⟨clock,hc⟩ := stridedTickCoordinateBindingSteps_polynomial tm r stride coordinate hv bound
  refine ⟨bound+addressBudget,clock,?_⟩
  intro n cs hb
  refine ⟨?_,hc n cs hb⟩
  intro q
  by_cases hq : q=r.target
  · subst q
    simp only [coordinateBindingProgramTemplate,Function.update_self,Polynomial.eval_add]
    exact (ha n cs hb).trans (Nat.le_add_left _ _)
  · simp only [coordinateBindingProgramTemplate,Function.update_of_ne hq,Polynomial.eval_add]
    exact (hb q).trans (Nat.le_add_right _ _)

/-- Resource bounds compose through the actual exit register file, with no supplied intermediate-value oracle. -/
theorem sequenceProgramTemplate_resources (p q : CounterProgramTemplate R) (bound middle budget clockP clockQ : Polynomial Nat)
    (hp : ∀ n (cs : R → Nat), (∀ r,cs r ≤ bound.eval n) →
      (∀ r,p.counters cs r ≤ middle.eval n) ∧ p.steps cs ≤ clockP.eval n)
    (hq : ∀ n (cs : R → Nat), (∀ r,cs r ≤ middle.eval n) →
      (∀ r,q.counters cs r ≤ budget.eval n) ∧ q.steps cs ≤ clockQ.eval n) :
    ∀ n (cs : R → Nat), (∀ r,cs r ≤ bound.eval n) →
      (∀ r,(sequenceProgramTemplate p q).counters cs r ≤ budget.eval n) ∧
      (sequenceProgramTemplate p q).steps cs ≤ (clockP+clockQ).eval n := by
  intro n cs hb
  obtain ⟨hm,hcp⟩ := hp n cs hb
  obtain ⟨hf,hcq⟩ := hq n (p.counters cs) hm
  exact ⟨hf,by simpa only [sequenceProgramTemplate,Polynomial.eval_add] using Nat.add_le_add hcp hcq⟩

end ShiReversibleGenerator
