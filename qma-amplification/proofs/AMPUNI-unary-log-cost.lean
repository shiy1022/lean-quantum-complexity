import «AMPUNI-unary-half»
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace ShiTMUnaryLogCost

/-- Numeric work budget for repeated halving. Each pass scans the current
unary stack, tests the produced stack, and changes the finite-state mode. -/
def work (n : Nat) : Nat :=
  if h : n < 2 then n + 2 else n + 2 + work (n / 2)
termination_by n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

theorem work_small {n : Nat} (h : n < 2) : work n = n + 2 := by
  rw [work, dif_pos h]

theorem work_large {n : Nat} (h : 2 ≤ n) :
    work n = n + 2 + work (n / 2) := by
  rw [work, dif_neg (by omega : ¬ n < 2)]

/-- The number of productive halvings equals the binary logarithm. -/
theorem log_step {n : Nat} (h : 2 ≤ n) :
    Nat.log 2 n = Nat.log 2 (n / 2) + 1 := by
  exact Nat.log_of_one_lt_of_le (by decide) h

theorem log_zero_of_small {n : Nat} (h : n < 2) : Nat.log 2 n = 0 := by
  exact Nat.log_eq_zero_iff.mpr (Or.inl h)

/-- The total scan-and-check work of all halving passes is linear in the
initial unary length. -/
theorem work_le_linear (n : Nat) : work n ≤ 4 * n + 4 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n < 2
      · rw [work_small hsmall]
        omega
      · have hn : 2 ≤ n := by omega
        have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
        rw [work_large hn]
        have hi := ih (n / 2) hlt
        omega

end ShiTMUnaryLogCost
