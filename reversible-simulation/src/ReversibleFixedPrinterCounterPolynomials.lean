import ReversiblePrinterMonotonicity

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- Exact counter polynomials for a fixed finite printer, including every intermediate node. -/
noncomputable def fixedPrinterCounterPolynomials (r : NodePrinterRegisters R) :
    List (FixedNodeTemplate R) → (R → Polynomial Nat) → (R → Polynomial Nat)
  | [], sizes => sizes
  | t :: ts, sizes => fixedPrinterCounterPolynomials r ts (t.countersPolynomial r sizes)

theorem fixedPrinterCounterPolynomials_eval (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (sizes : R → Polynomial Nat) (n : Nat) :
    (fun s => (fixedPrinterCounterPolynomials r ts sizes s).eval n) =
      fixedNodeCounters r ts (fun s => (sizes s).eval n) := by
  induction ts generalizing sizes with
  | nil => rfl
  | cons t ts ih =>
      rw [fixedPrinterCounterPolynomials, ih, FixedNodeTemplate.countersPolynomial_eval]
      rfl

theorem fixedNodeCounters_mono (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) :
    ∀ s, fixedNodeCounters r ts cs s ≤ fixedNodeCounters r ts ds s := by
  induction ts generalizing cs ds with
  | nil => exact h
  | cons t ts ih => exact ih _ _ (t.counters_mono r cs ds h)

end ShiReversibleGenerator
