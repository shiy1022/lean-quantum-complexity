import ReversibleFixedNodeProgramTemplate
import ReversibleFixedPrinterCounterPolynomials

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- A fixed finite printer has a polynomial bound on every actual exit counter. -/
theorem fixedNodeProgramTemplate_budget (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (bound : Polynomial Nat) : ∃ budget : Polynomial Nat, ∀ n (cs : R → Nat),
    (∀ q,cs q ≤ bound.eval n) → ∀ q,(fixedNodeProgramTemplate r ts).counters cs q ≤ budget.eval n := by
  classical
  let sizes : R → Polynomial Nat := fun _ => bound
  let final := fixedPrinterCounterPolynomials r ts sizes
  refine ⟨∑ q,final q,?_⟩
  intro n cs hb q
  have hm := fixedNodeCounters_mono r ts cs (fun z => (sizes z).eval n) hb q
  have he := congrFun (fixedPrinterCounterPolynomials_eval r ts sizes n) q
  have hs : (final q).eval n ≤ (∑ z,final z).eval n := by
    rw [Polynomial.eval_finsetSum]
    exact Finset.single_le_sum (fun z _ => Nat.zero_le ((final z).eval n)) (Finset.mem_univ q)
  exact (hm.trans (by simpa only [final] using he.ge)).trans hs

end ShiReversibleGenerator
