import «AMPUNI-centered-gap»
import «AMPUNI-constructive-schedule»

set_option autoImplicit false

namespace ShiQMACenteredGap
open ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem biasIter_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) (r : Nat) : biasIter d r ≤ biasIter e r := by
  induction r with
  | zero => exact hde
  | succ r ih =>
    exact biasStep_mono (biasIter_bounds hd (hde.trans he) r).1 ih
      (biasIter_bounds (hd.trans hde) he r).2

theorem biasIter_add (d : ℝ) (r s : Nat) :
    biasIter d (r + s) = biasIter (biasIter d r) s := by
  induction s with
  | zero => rfl
  | succ s ih => exact congrArg biasStep ih

theorem biasIter_standard (r : Nat) :
    biasIter (1 / 6) r = 1 / 2 - error r := by
  induction r with
  | zero => norm_num [biasIter, error]
  | succ r ih =>
    simp only [biasIter, ih, error, biasStep, majorityError]
    ring

/-- A schedule in the same affine-logarithmic form as the existing concrete controller. -/
def normalizationRounds (q : Polynomial ℕ) (n : Nat) : Nat :=
  3 * rounds q n

/-- Normalize the initial bias, then run the existing exponential-error schedule. -/
def generalGapRounds (q p : Polynomial ℕ) (n : Nat) : Nat :=
  normalizationRounds q n + rounds p n

theorem normalizationRounds_suffice {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (normalizationRounds q n) := by
  have hbudget : q.eval n ≤ 2 ^ rounds q n :=
    (eval_le_pow_budget q n).trans (Nat.pow_le_pow_right (by decide) (by
      dsimp [rounds]; omega))
  have hreal : (↑(q.eval n) : ℝ) ≤ (2 : ℝ) ^ rounds q n := by exact_mod_cast hbudget
  have h := biasIter_dyadic hd hd' (rounds q n)
  rw [min_eq_left (hgap.trans (mul_le_mul_of_nonneg_right hreal hd))] at h
  exact h

/-- Scalar amplification from an inverse-polynomial centered gap to any polynomial error exponent. -/
theorem generalGapRounds_suffice {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q p : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    1 / 2 - ((1 : ℝ) / 2) ^ (p.eval n) ≤ biasIter d (generalGapRounds q p n) := by
  have hn := normalizationRounds_suffice hd hd' q n hgap
  have hm := biasIter_mono (by norm_num : (0 : ℝ) ≤ 1 / 6) hn
    (biasIter_bounds hd hd' (normalizationRounds q n)).2 (rounds p n)
  rw [biasIter_standard] at hm
  rw [generalGapRounds, biasIter_add]
  have he := error_rounds p n
  linarith

theorem generalGapRounds_controller_form (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n =
      (3 * (Nat.log 2 (q.eval 1 + 1) + 4) + Nat.log 2 (p.eval 1 + 1) + 4) +
      (3 * q.natDegree + p.natDegree) * (Nat.log 2 (n + 1) + 1) := by
  dsimp [generalGapRounds, normalizationRounds, rounds, exponentBudget]
  ring

/-- The full scalar schedule has polynomial copy overhead in input length. -/
theorem copies_generalGapRounds_le (q p : Polynomial ℕ) (n : Nat) :
    3 ^ generalGapRounds q p n ≤
      (3 ^ (Nat.log 2 (q.eval 1 + 1) + q.natDegree + 4) *
        (n + 1) ^ (2 * q.natDegree)) ^ 3 *
      (3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree)) := by
  have hq := Nat.pow_le_pow_left (copies_rounds_le q n) 3
  have hp := copies_rounds_le p n
  dsimp [generalGapRounds, normalizationRounds]
  rw [pow_add, Nat.mul_comm 3 (rounds q n), pow_mul]
  exact Nat.mul_le_mul hq hp

end ShiQMACenteredGap

#print axioms ShiQMACenteredGap.generalGapRounds_suffice
#print axioms ShiQMACenteredGap.copies_generalGapRounds_le
