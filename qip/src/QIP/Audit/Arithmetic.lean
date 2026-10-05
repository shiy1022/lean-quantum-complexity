import QIP.Arithmetic.Repetition

/-! Fresh-import audit for Q33: exact statement types, then transitive axioms. -/

open ShiQIP.Arith

#check (halving_gap : ∀ {ε : ℝ}, ε ≤ 1 → (1 + Real.sqrt (1 - ε)) / 2 ≤ 1 - ε / 4)
#check (halving_iterate : ∀ {s : ℕ → ℝ} {ε : ℝ}, ε ≤ 1 → s 0 ≤ 1 - ε →
  (∀ i, s (i + 1) ≤ (1 + Real.sqrt (s i)) / 2) → ∀ r : ℕ, s r ≤ 1 - ε / 4 ^ r)
#check (bell_soundness_constant : (1 : ℝ) - (1 / 2 - 1 / 3) ^ 2 = 35 / 36)
#check (four_pow_le_padM_sq : ∀ r : ℕ, 4 ^ r ≤ (2 ^ (r + 1) + 1) ^ 2)
#check (halfCount_iterate_padM : ∀ r : ℕ, halfCount^[r] (padM r) = 3)
#check (le_padCount : ∀ m : ℕ, m ≤ padCount m)
#check (padCount_le : ∀ m : ℕ, padCount m ≤ 2 * m + 3)
#check (padExp_eq_zero_iff : ∀ m : ℕ, padExp m = 0 ↔ m ≤ 3)
#check (one_sub_pow_le_inv : ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ 1 → ∀ k : ℕ,
  (1 - δ) ^ k ≤ 1 / (1 + k * δ))
#check (repK_mul_repδ : ∀ {M : ℕ}, M ≠ 0 → (repK M : ℝ) * repδ M = 2)
#check (repetition_bound : ∀ {M : ℕ}, 1 ≤ M → (1 - 1 / (36 * (M : ℝ) ^ 2)) ^ (72 * M ^ 2) ≤ 1 / 3)
#check (repK_le_poly : ∀ {p : Polynomial ℕ} {M n : ℕ}, M ≤ p.eval n →
  repK M ≤ (72 * p ^ 2).eval n)
#check (soundness_schedule : ∀ {s : ℕ → ℝ}, s 0 ≤ 35 / 36 →
  (∀ i, s (i + 1) ≤ (1 + Real.sqrt (s i)) / 2) → ∀ r : ℕ, 0 ≤ s r →
  s r ^ repK (padM r) ≤ 1 / 3)

#print axioms ShiQIP.Arith.halving_gap
#print axioms ShiQIP.Arith.halving_step
#print axioms ShiQIP.Arith.halving_iterate
#print axioms ShiQIP.Arith.bell_soundness_constant
#print axioms ShiQIP.Arith.bell_gap
#print axioms ShiQIP.Arith.three_le_padM
#print axioms ShiQIP.Arith.padM_odd
#print axioms ShiQIP.Arith.halfCount_padM_succ
#print axioms ShiQIP.Arith.halfCount_iterate_padM
#print axioms ShiQIP.Arith.four_pow_le_padM_sq
#print axioms ShiQIP.Arith.four_pow_le_padM_sq_real
#print axioms ShiQIP.Arith.le_padCount
#print axioms ShiQIP.Arith.three_le_padCount
#print axioms ShiQIP.Arith.padExp_eq_zero_iff
#print axioms ShiQIP.Arith.padCount_le
#print axioms ShiQIP.Arith.padCount_le_poly
#print axioms ShiQIP.Arith.one_sub_pow_le_inv
#print axioms ShiQIP.Arith.repδ_le_one
#print axioms ShiQIP.Arith.repK_mul_repδ
#print axioms ShiQIP.Arith.repetition_bound
#print axioms ShiQIP.Arith.repeated_soundness
#print axioms ShiQIP.Arith.repK_le_poly
#print axioms ShiQIP.Arith.compressed_gap
#print axioms ShiQIP.Arith.soundness_schedule
