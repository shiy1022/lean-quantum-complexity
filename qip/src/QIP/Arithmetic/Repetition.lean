/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Arithmetic.Gap
import QIP.Arithmetic.Padding

/-!
# Q33 — the concrete all-pass repetition schedule

With padded message count `M ≥ 1`, set `δ = 1 / (36 M²)` and `K = 72 M²`. Then `K δ = 2` and
`(1 - δ) ^ K ≤ 1 / (1 + K δ) = 1 / 3`. The chain from the Bell-test soundness `35/36` through `r`
halvings (`padM r` messages) to final soundness `1/3` is `soundness_schedule`.
-/

namespace ShiQIP.Arith

/-- `(1 - δ) ^ k ≤ 1 / (1 + k δ)` for `0 ≤ δ ≤ 1`, via Bernoulli for `(1 + δ) ^ k`. -/
theorem one_sub_pow_le_inv {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    (1 - δ) ^ k ≤ 1 / (1 + k * δ) := by
  have hB : 1 + k * δ ≤ (1 + δ) ^ k := one_add_mul_le_pow (by linarith) k
  have hprod : (1 - δ) ^ k * (1 + δ) ^ k ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : 0 < 1 + k * δ := by positivity
  rw [le_div_iff₀ hpos]
  calc (1 - δ) ^ k * (1 + k * δ) ≤ (1 - δ) ^ k * (1 + δ) ^ k :=
        mul_le_mul_of_nonneg_left hB (pow_nonneg (by linarith) _)
    _ ≤ 1 := hprod

/-- The number of parallel copies for padded message count `M`. -/
def repK (M : ℕ) : ℕ := 72 * M ^ 2

/-- The soundness gap left after compressing to three messages from padded count `M`. -/
noncomputable def repδ (M : ℕ) : ℝ := 1 / (36 * (M : ℝ) ^ 2)

theorem repδ_nonneg (M : ℕ) : 0 ≤ repδ M := by unfold repδ; positivity

theorem repδ_le_one {M : ℕ} (hM : 1 ≤ M) : repδ M ≤ 1 := by
  unfold repδ
  have : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rw [div_le_one (by positivity)]
  nlinarith

theorem repK_mul_repδ {M : ℕ} (hM : M ≠ 0) : (repK M : ℝ) * repδ M = 2 := by
  have : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  unfold repK repδ
  push_cast
  field_simp
  norm_num

/-- `(1 - δ) ^ K ≤ 1 / 3` for the concrete schedule. -/
theorem repetition_bound {M : ℕ} (hM : 1 ≤ M) : (1 - repδ M) ^ repK M ≤ 1 / 3 := by
  have h := one_sub_pow_le_inv (repδ_nonneg M) (repδ_le_one hM) (repK M)
  rw [repK_mul_repδ (by omega)] at h
  norm_num at h ⊢
  exact h

/-- Any soundness `s ∈ [0, 1 - δ]` is driven to at most `1/3` by `K` all-pass copies. -/
theorem repeated_soundness {M : ℕ} (hM : 1 ≤ M) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 - repδ M) :
    s ^ repK M ≤ 1 / 3 :=
  (pow_le_pow_left₀ hs0 hs _).trans (repetition_bound hM)

/-- A polynomial bound on `M` gives a polynomial bound on `K`. -/
theorem repK_le_poly {p : Polynomial ℕ} {M n : ℕ} (hM : M ≤ p.eval n) :
    repK M ≤ (72 * p ^ 2).eval n := by
  simp only [repK, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 2)

/-- The gap after `r` halvings from soundness `1 - ε` dominates `ε / M²` for `M = padM r`. -/
theorem compressed_gap {ε : ℝ} (h0 : 0 ≤ ε) (r : ℕ) :
    1 - ε / 4 ^ r ≤ 1 - ε / (padM r : ℝ) ^ 2 := by
  have h4 : (0 : ℝ) < 4 ^ r := by positivity
  have := div_le_div_of_nonneg_left h0 h4 (four_pow_le_padM_sq_real r)
  linarith

/-- **The scalar endgame.** Start from soundness `35/36` (the Bell test), apply `r` halving
steps `s (i+1) ≤ (1 + √(s i)) / 2`, then `K = 72 (padM r)²` all-pass copies: the final
soundness is at most `1/3`. -/
theorem soundness_schedule {s : ℕ → ℝ} (hs0 : s 0 ≤ 35 / 36)
    (hstep : ∀ i, s (i + 1) ≤ (1 + Real.sqrt (s i)) / 2) (r : ℕ) (hpos : 0 ≤ s r) :
    s r ^ repK (padM r) ≤ 1 / 3 := by
  have hM : 1 ≤ padM r := le_trans (by norm_num) (three_le_padM r)
  have h1 := halving_iterate (ε := 1 / 36) (by norm_num)
    (by rw [← bell_gap]; exact hs0) hstep r
  have h2 := compressed_gap (ε := 1 / 36) (by norm_num) r
  refine repeated_soundness hM hpos ?_
  unfold repδ
  have : (1 / 36 : ℝ) / (padM r : ℝ) ^ 2 = 1 / (36 * (padM r : ℝ) ^ 2) := by
    rw [div_div]
  linarith

end ShiQIP.Arith
