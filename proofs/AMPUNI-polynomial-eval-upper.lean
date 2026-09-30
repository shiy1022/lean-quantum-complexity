import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace ShiQMAPolynomialBound

/-- A fixed natural-coefficient polynomial is bounded by its coefficient sum
times one power of `n+1`. This supports a computable logarithmic round
schedule based on a fixed degree and coefficient bound. -/
theorem eval_le_coeffSum_mul (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  classical
  have hpow (i : ℕ) (hi : i ∈ p.support) :
      n ^ i ≤ (n + 1) ^ p.natDegree := by
    calc
      n ^ i ≤ (n + 1) ^ i :=
        Nat.pow_le_pow_left (Nat.le_succ n) i
      _ ≤ (n + 1) ^ p.natDegree :=
        Nat.pow_le_pow_right (by omega)
          (Polynomial.le_natDegree_of_mem_supp i hi)
  have hs :
      (∑ i ∈ p.support, p.coeff i * n ^ i) ≤
        ∑ i ∈ p.support,
          p.coeff i * (n + 1) ^ p.natDegree := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.mul_le_mul_left _ (hpow i hi)
  calc
    p.eval n = ∑ i ∈ p.support, p.coeff i * n ^ i := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
    _ ≤ ∑ i ∈ p.support,
        p.coeff i * (n + 1) ^ p.natDegree := hs
    _ = p.eval 1 * (n + 1) ^ p.natDegree := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
      simp

end ShiQMAPolynomialBound
