import ReversibleConditionalPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

noncomputable instance conditionalPrinterFintype (r : NodePrinterRegisters R)
    (yes no : List (FixedNodeTemplate R)) (a b ca cb : R) [Fintype L] :
    Fintype (ConditionalPrinterLabels r yes no a b ca cb L) := inferInstance

/-- One polynomial bounds either runtime branch, including the actual preserved comparison. -/
theorem conditionalPrinter_polynomial_bound (r : NodePrinterRegisters R)
    (yes no : List (FixedNodeTemplate R)) (a b ca cb : R) (hbc : b ≠ ca)
    (sizes : R → Polynomial Nat) : ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat),
    (∀ s, cs s ≤ (sizes s).eval n) →
    operationSteps (comparisonCopies a b ca cb) cs + comparisonSteps (cs a) (cs b) +
      fixedNodeSteps r (if cs a ≤ cs b then yes else no) cs ≤ clock.eval n := by
  refine ⟨Polynomial.C 11 * (sizes a + sizes b) + Polynomial.C 7 +
    fixedNodeClock r yes sizes + fixedNodeClock r no sizes, ?_⟩
  intro n cs h
  have hy := fixedNodeSteps_polynomial_bound r yes sizes n cs h
  have hn := fixedNodeSteps_polynomial_bound r no sizes n cs h
  have hc := comparisonSteps_bound (cs a) (cs b)
  have ha := h a
  have hb := h b
  rw [comparisonCopies_steps a b ca cb hbc]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  split_ifs <;> omega

end ShiReversibleGenerator
