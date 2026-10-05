/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Mathlib

/-!
# Q33 — scalar gap bounds for one halving step

The compression step of the QIP(3) proof turns a protocol of value `s` into one of value at most
`(1 + √s) / 2`. This file proves the protocol-independent arithmetic: such a step costs at most a
factor four of the soundness gap, so `r` steps from soundness `1 - ε` give soundness
`1 - ε / 4 ^ r`. It also records the perfect-completeness constant `35/36`.
-/

namespace ShiQIP.Arith

/-- One halving step loses at most a factor four of the gap (for any `ε ≤ 1`). -/
theorem halving_gap {ε : ℝ} (h1 : ε ≤ 1) :
    (1 + Real.sqrt (1 - ε)) / 2 ≤ 1 - ε / 4 := by
  have h : Real.sqrt (1 - ε) ≤ 1 - ε / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [sq_nonneg ε]
  linarith

/-- The monotone form used in the compression induction. -/
theorem halving_step {s ε : ℝ} (h1 : ε ≤ 1) (hs : s ≤ 1 - ε) :
    (1 + Real.sqrt s) / 2 ≤ 1 - ε / 4 := by
  have := Real.sqrt_le_sqrt hs
  linarith [halving_gap h1]

/-- `r` halving steps from soundness `1 - ε` give soundness `1 - ε / 4 ^ r`. The sequence `s`
need not be nonnegative; `Real.sqrt` is monotone everywhere. -/
theorem halving_iterate {s : ℕ → ℝ} {ε : ℝ} (h1 : ε ≤ 1) (hs0 : s 0 ≤ 1 - ε)
    (hstep : ∀ i, s (i + 1) ≤ (1 + Real.sqrt (s i)) / 2) (r : ℕ) :
    s r ≤ 1 - ε / 4 ^ r := by
  induction r with
  | zero => simpa using hs0
  | succ r ih =>
    have hp : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num)
    have he1 : ε / 4 ^ r ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc s (r + 1) ≤ (1 + Real.sqrt (s r)) / 2 := hstep r
      _ ≤ 1 - ε / 4 ^ r / 4 := halving_step he1 ih
      _ = 1 - ε / 4 ^ (r + 1) := by rw [pow_succ, div_div]

/-- The soundness gap left by the half-threshold Bell test: `1 - (1/2 - 1/3)^2 = 35/36`. -/
theorem bell_soundness_constant : (1 : ℝ) - (1 / 2 - 1 / 3) ^ 2 = 35 / 36 := by norm_num

/-- The corresponding gap: soundness `35/36` is soundness `1 - 1/36`. -/
theorem bell_gap : (35 / 36 : ℝ) = 1 - 1 / 36 := by norm_num

end ShiQIP.Arith
