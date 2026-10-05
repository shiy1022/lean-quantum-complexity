/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Mathlib

/-!
# Q33 — message-count padding

Compression needs `M = 2 ^ (r + 1) + 1` messages; one halving maps `2 ^ (r + 2) + 1` messages to
`2 ^ (r + 1) + 1`, and `r = 0` is the three-message base case. A protocol with `m` messages is
padded to the least such count at or above `m` (`padCount m`), which is at most `2 * m + 3`. The
bound holds for every `m`, including `0` and `1`. `4 ^ r ≤ M ^ 2` converts the per-step gap loss
into a loss in terms of the padded count.
-/

namespace ShiQIP.Arith

/-- The padded message count with halving exponent `r`. -/
def padM (r : ℕ) : ℕ := 2 ^ (r + 1) + 1

theorem padM_zero : padM 0 = 3 := rfl

theorem three_le_padM (r : ℕ) : 3 ≤ padM r := by
  have : 2 ≤ 2 ^ (r + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold padM; omega

theorem padM_odd (r : ℕ) : padM r % 2 = 1 := by
  unfold padM; rw [pow_succ]; omega

/-- The message count after one halving: `M ↦ (M - 1) / 2 + 1`. -/
def halfCount (M : ℕ) : ℕ := (M - 1) / 2 + 1

/-- One halving maps `2 ^ (r + 2) + 1` messages to `2 ^ (r + 1) + 1`. -/
theorem halfCount_padM_succ (r : ℕ) : halfCount (padM (r + 1)) = padM r := by
  unfold halfCount padM
  rw [pow_succ 2 (r + 1)]
  omega

/-- `r` halvings take `padM r` messages to exactly three. -/
theorem halfCount_iterate_padM (r : ℕ) : halfCount^[r] (padM r) = 3 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, halfCount_padM_succ, ih]

theorem four_pow_le_padM_sq (r : ℕ) : 4 ^ r ≤ padM r ^ 2 := by
  have h4 : (4 : ℕ) ^ r = (2 ^ r) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  apply Nat.pow_le_pow_left
  unfold padM
  rw [pow_succ]; omega

theorem four_pow_le_padM_sq_real (r : ℕ) : (4 : ℝ) ^ r ≤ (padM r : ℝ) ^ 2 := by
  exact_mod_cast four_pow_le_padM_sq r

theorem exists_padExp (m : ℕ) : ∃ r, m ≤ padM r :=
  ⟨m, by have := Nat.lt_two_pow_self (n := m + 1); unfold padM; omega⟩

/-- The least halving exponent whose padded count is at least `m`. -/
def padExp (m : ℕ) : ℕ := Nat.find (exists_padExp m)

/-- The padded message count for an `m`-message protocol. -/
def padCount (m : ℕ) : ℕ := padM (padExp m)

theorem le_padCount (m : ℕ) : m ≤ padCount m := Nat.find_spec (exists_padExp m)

theorem three_le_padCount (m : ℕ) : 3 ≤ padCount m := three_le_padM _

theorem padExp_eq_zero_iff (m : ℕ) : padExp m = 0 ↔ m ≤ 3 := by
  unfold padExp
  rw [Nat.find_eq_zero]
  rfl

/-- Padding at most doubles the message count (plus three, so `m = 0, 1` are covered). -/
theorem padCount_le (m : ℕ) : padCount m ≤ 2 * m + 3 := by
  unfold padCount
  rcases h : padExp m with _ | k
  · simp [padM]
  · have hmin : ¬ m ≤ padM k :=
      Nat.find_min (exists_padExp m) (m := k) (by unfold padExp at h; omega)
    unfold padM at hmin ⊢
    rw [pow_succ 2 (k + 1)]
    omega

/-- A polynomial bound on the message count gives a polynomial bound on the padded count. -/
theorem padCount_le_poly {p : Polynomial ℕ} {m n : ℕ} (hm : m ≤ p.eval n) :
    padCount m ≤ (2 * p + 3).eval n := by
  have := padCount_le m
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  omega

end ShiQIP.Arith
