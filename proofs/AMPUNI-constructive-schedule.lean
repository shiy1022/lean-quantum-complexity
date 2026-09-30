import «AMPUNI-polynomial-eval-upper»
import «AMPUNI-error-iteration»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAConstructiveSchedule
open ShiQMAErrorIteration

/-- A logarithmic budget using only a fixed coefficient bound, a fixed
degree, and the logarithm of the input length plus one. -/
def exponentBudget (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  Nat.log 2 (p.eval 1 + 1) + 1 +
    p.natDegree * (Nat.log 2 (n + 1) + 1)

def rounds (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  exponentBudget p n + 3

theorem eval_le_pow_budget (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ 2 ^ exponentBudget p n := by
  let A := Nat.log 2 (p.eval 1 + 1) + 1
  let B := Nat.log 2 (n + 1) + 1
  have hc : p.eval 1 ≤ 2 ^ A := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
      (p.eval 1 + 1)
    dsimp [A]
    omega
  have hn : n + 1 ≤ 2 ^ B := by
    exact Nat.le_of_lt
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 1))
  have hpow : (n + 1) ^ p.natDegree ≤
      (2 ^ B) ^ p.natDegree :=
    Nat.pow_le_pow_left hn p.natDegree
  calc
    p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree :=
      ShiQMAPolynomialBound.eval_le_coeffSum_mul p n
    _ ≤ 2 ^ A * (2 ^ B) ^ p.natDegree :=
      Nat.mul_le_mul hc hpow
    _ = 2 ^ exponentBudget p n := by
      have hpoweq : (2 ^ B) ^ p.natDegree =
          2 ^ (B * p.natDegree) :=
        (pow_mul 2 B p.natDegree).symm
      rw [hpoweq, ← pow_add]
      congr 1
      dsimp [exponentBudget, A, B]
      ring

theorem error_rounds (p : Polynomial ℕ) (n : ℕ) :
    error (rounds p n) ≤ ((1 : ℝ) / 2) ^ (p.eval n) := by
  have h := dyadic_error_bound (exponentBudget p n)
  have hp := pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1)
    (eval_le_pow_budget p n)
  exact h.trans hp

/-- The same constructive schedule still requires only polynomially many
copies for each fixed `p`. -/
theorem copies_rounds_le (p : Polynomial ℕ) (n : ℕ) :
    3 ^ rounds p n ≤
      3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree) := by
  let A := Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4
  let L := Nat.log 2 (n + 1)
  have hlog : 2 ^ L ≤ n + 1 :=
    Nat.pow_log_le_self 2 (by omega : n + 1 ≠ 0)
  have hbase : 3 ^ L ≤ 4 ^ L :=
    Nat.pow_le_pow_left (by decide : 3 ≤ 4) L
  have hsq : (2 ^ L) ^ 2 ≤ (n + 1) ^ 2 :=
    Nat.pow_le_pow_left hlog 2
  have heq : 4 ^ L = (2 ^ L) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
    exact (pow_mul 2 2 L).symm
  have hunit : 3 ^ L ≤ (n + 1) ^ 2 := by
    rw [heq] at hbase
    exact hbase.trans hsq
  have hpow : (3 ^ L) ^ p.natDegree ≤
      ((n + 1) ^ 2) ^ p.natDegree :=
    Nat.pow_le_pow_left hunit p.natDegree
  have hid : rounds p n = A + L * p.natDegree := by
    dsimp [rounds, exponentBudget, A, L]
    ring
  rw [hid, pow_add, pow_mul]
  change 3 ^ A * (3 ^ L) ^ p.natDegree ≤
    3 ^ A * (n + 1) ^ (2 * p.natDegree)
  rw [pow_mul]
  exact Nat.mul_le_mul_left _ hpow

end ShiQMAConstructiveSchedule
