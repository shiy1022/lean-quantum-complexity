import ReversiblePolynomialMajorant

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Every natural-coefficient polynomial is monotone on natural inputs. -/
theorem naturalPolynomial_eval_mono (p : Polynomial Nat) (a b : Nat) (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  classical
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum,Polynomial.sum_def,Polynomial.sum_def]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

end ShiReversibleGenerator
