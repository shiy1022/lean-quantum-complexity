import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-- A fixed natural-coefficient polynomial is bounded by its coefficient sum
times one power of `n+1`. -/
theorem ShiQMAPolynomialBound.eval_le_coeffSum_mul (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  sorry
