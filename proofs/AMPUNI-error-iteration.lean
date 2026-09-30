import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ShiQMAErrorIteration

/-- Failure probability of a majority of three independent trials. -/
def majorityError (e : ℝ) : ℝ := 3 * e ^ 2 - 2 * e ^ 3

/-- The scalar error recurrence, starting at the usual QMA error threshold. -/
noncomputable def error : Nat → ℝ
  | 0 => 1 / 3
  | r + 1 => majorityError (error r)

private theorem majorityError_bounds {e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1 / 3) :
    0 ≤ majorityError e ∧ majorityError e ≤ e := by
  constructor
  · have h := mul_nonneg (sq_nonneg e) (show 0 ≤ 3 - 2 * e by linarith)
    dsimp [majorityError]
    nlinarith
  · have h := mul_nonneg
      (mul_nonneg he (show 0 ≤ 1 - e by linarith))
      (show 0 ≤ 1 - 2 * e by linarith)
    dsimp [majorityError]
    nlinarith

theorem error_bounds (r : Nat) : 0 ≤ error r ∧ error r ≤ 1 / 3 := by
  induction r with
  | zero => norm_num [error]
  | succ r ih =>
      have h := majorityError_bounds ih.1 ih.2
      exact ⟨h.1, h.2.trans ih.2⟩

private theorem majorityError_square_bound {e : ℝ} (he : 0 ≤ e) :
    3 * majorityError e ≤ (3 * e) ^ 2 := by
  have h := mul_nonneg he (sq_nonneg e)
  dsimp [majorityError]
  nlinarith

/-- After the first round the scaled error squares at every further round. -/
theorem scaled_error_bound (r : Nat) :
    3 * error (r + 1) ≤ ((7 : ℝ) / 9) ^ (2 ^ r) := by
  induction r with
  | zero => norm_num [error, majorityError]
  | succ r ih =>
      have h := majorityError_square_bound (error_bounds (r + 1)).1
      have hs := pow_le_pow_left₀
        (show 0 ≤ 3 * error (r + 1) by linarith [(error_bounds (r + 1)).1]) ih 2
      change 3 * majorityError (error (r + 1)) ≤ ((7 : ℝ) / 9) ^ (2 ^ (r + 1))
      rw [pow_succ, pow_mul]
      exact h.trans hs

/-- Three initial rounds give a dyadic bound, then each round doubles the exponent. -/
theorem dyadic_error_bound (r : Nat) :
    error (r + 3) ≤ ((1 : ℝ) / 2) ^ (2 ^ r) := by
  have h := scaled_error_bound (r + 2)
  have hp : ((7 : ℝ) / 9) ^ (2 ^ (r + 2)) =
      (((7 : ℝ) / 9) ^ 4) ^ (2 ^ r) := by
    rw [pow_add, show (2 : Nat) ^ 2 = 4 by norm_num, Nat.mul_comm, pow_mul]
  rw [hp] at h
  have hq := pow_le_pow_left₀
    (show 0 ≤ ((7 : ℝ) / 9) ^ 4 from pow_nonneg (by norm_num) _)
    (show ((7 : ℝ) / 9) ^ 4 ≤ 1 / 2 by norm_num) (2 ^ r)
  have he := (error_bounds (r + 3)).1
  have h' : 3 * error (r + 3) ≤ ((1 : ℝ) / 2) ^ (2 ^ r) := by
    simpa only [Nat.add_assoc] using h.trans hq
  linarith

/-- A logarithmic number of rounds suffices for the target exponential error. -/
def roundsFor (m : Nat) : Nat := Nat.log 2 m + 4

theorem error_roundsFor (m : Nat) : error (roundsFor m) ≤ ((1 : ℝ) / 2) ^ m := by
  have h := dyadic_error_bound (Nat.log 2 m + 1)
  have hm : m ≤ 2 ^ (Nat.log 2 m + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m)
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1) hm
  exact (show error (roundsFor m) ≤ ((1 : ℝ) / 2) ^ (2 ^ (Nat.log 2 m + 1)) from h).trans hp

/-- The number of copies required by these rounds is polynomial in the target exponent. -/
theorem copies_roundsFor_le (m : Nat) (hm : 0 < m) : 3 ^ roundsFor m ≤ 81 * m ^ 2 := by
  have hlog := Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
  have hbase : 3 ^ Nat.log 2 m ≤ 4 ^ Nat.log 2 m :=
    Nat.pow_le_pow_left (by decide : 3 ≤ 4) _
  have hsq : (2 ^ Nat.log 2 m) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlog 2
  have heq : 4 ^ Nat.log 2 m = (2 ^ Nat.log 2 m) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
    exact (pow_mul 2 2 (Nat.log 2 m)).symm
  rw [heq] at hbase
  dsimp [roundsFor]
  rw [pow_add]
  norm_num only [show (3 : Nat) ^ 4 = 81 by norm_num]
  nlinarith

end ShiQMAErrorIteration

-- Keep the numerical proof's dependency check alongside its standalone build.
#print axioms ShiQMAErrorIteration.error_roundsFor
#print axioms ShiQMAErrorIteration.copies_roundsFor_le
