import «AMPUNI-error-iteration»
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ShiQMACenteredGap
open ShiQMAErrorIteration

/-- Majority of three acts on displacement from acceptance probability one half. -/
noncomputable def biasStep (d : ℝ) : ℝ := 3 / 2 * d - 2 * d ^ 3

theorem majority_centered (d : ℝ) :
    majorityError (1 / 2 + d) = 1 / 2 + biasStep d := by
  dsimp [majorityError, biasStep]
  ring

theorem majority_complement (x : ℝ) :
    majorityError (1 - x) = 1 - majorityError x := by
  dsimp [majorityError]
  ring

theorem biasStep_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) : biasStep d ≤ biasStep e := by
  have hed : e * d ≤ 1 / 4 := by nlinarith [sq_nonneg (e - d)]
  have hsq : e ^ 2 + e * d + d ^ 2 ≤ 3 / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ e by linarith) (show 0 ≤ 1 / 2 - e by linarith),
      mul_nonneg hd (show 0 ≤ 1 / 2 - d by linarith)]
  have h := mul_nonneg (show 0 ≤ e - d by linarith)
    (show 0 ≤ 3 / 2 - 2 * (e ^ 2 + e * d + d ^ 2) by linarith)
  dsimp [biasStep]
  nlinarith

theorem biasStep_bounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) :
    0 ≤ biasStep d ∧ biasStep d ≤ 1 / 2 := by
  constructor
  · have h := biasStep_mono (d := 0) (e := d) (by norm_num) hd hd'
    norm_num [biasStep] at h ⊢
    exact h
  · have h := biasStep_mono hd hd' (le_refl (1 / 2))
    norm_num [biasStep] at h ⊢
    exact h

/-- Until a constant bias is reached, every majority round grows the bias geometrically. -/
theorem biasStep_growth {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 6) :
    (4 / 3 : ℝ) * d ≤ biasStep d := by
  have hs : d ^ 2 ≤ 1 / 36 := by nlinarith
  have h := mul_nonneg hd (show 0 ≤ 1 / 6 - 2 * d ^ 2 by linarith)
  dsimp [biasStep]
  nlinarith

theorem biasStep_capped_growth {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) :
    min (1 / 6) ((4 / 3 : ℝ) * d) ≤ biasStep d := by
  by_cases h : d ≤ 1 / 6
  · exact (min_le_right _ _).trans (biasStep_growth hd h)
  · have hmono := biasStep_mono (d := 1 / 6) (e := d) (by norm_num) (by linarith) hd'
    have hconst : (1 / 6 : ℝ) ≤ biasStep (1 / 6) := by norm_num [biasStep]
    exact (min_le_left _ _).trans (hconst.trans hmono)

noncomputable def biasIter (d : ℝ) : Nat → ℝ
  | 0 => d
  | r + 1 => biasStep (biasIter d r)

theorem biasIter_bounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    0 ≤ biasIter d r ∧ biasIter d r ≤ 1 / 2 := by
  induction r with
  | zero => exact ⟨hd, hd'⟩
  | succ r ih => exact biasStep_bounds ih.1 ih.2

theorem biasIter_growth {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) (((4 : ℝ) / 3) ^ r * d) ≤ biasIter d r := by
  induction r with
  | zero => simpa [biasIter] using min_le_right (1 / 6 : ℝ) d
  | succ r ih =>
    have hb := biasIter_bounds hd hd' r
    have hg := biasStep_capped_growth hb.1 hb.2
    change min (1 / 6) (((4 : ℝ) / 3) ^ (r + 1) * d) ≤ biasStep (biasIter d r)
    rw [pow_succ]
    by_cases h : (1 / 6 : ℝ) ≤ ((4 : ℝ) / 3) ^ r * d
    · rw [min_eq_left h] at ih
      have hcap : (1 / 6 : ℝ) ≤ (4 / 3) * biasIter d r := by linarith
      rw [min_eq_left hcap] at hg
      exact (min_le_left _ _).trans hg
    · rw [min_eq_right (le_of_not_ge h)] at ih
      apply le_trans _ hg
      apply min_le_min_left
      nlinarith

/-- Three rounds suffice for each factor of two in the initial inverse bias. -/
theorem biasIter_dyadic {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) ((2 : ℝ) ^ r * d) ≤ biasIter d (3 * r) := by
  have hp : (2 : ℝ) ^ r ≤ ((4 : ℝ) / 3) ^ (3 * r) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
  exact (min_le_min_left _ (mul_le_mul_of_nonneg_right hp hd)).trans
    (biasIter_growth hd hd' (3 * r))

/-- A concrete logarithmic schedule for a bias at least 1/(6q). -/
def gapRounds (q : Nat) : Nat := 3 * (Nat.log 2 q + 1)

theorem biasIter_gapRounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Nat) (hgap : (1 / 6 : ℝ) ≤ (q : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (gapRounds q) := by
  have hq : q ≤ 2 ^ (Nat.log 2 q + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) q)
  have hqr : (q : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 q + 1) := by exact_mod_cast hq
  have h := biasIter_dyadic hd hd' (Nat.log 2 q + 1)
  rw [min_eq_left (hgap.trans (mul_le_mul_of_nonneg_right hqr hd))] at h
  exact h

/-- The logarithmic normalization schedule uses at most polynomially many copies. -/
theorem copies_gapRounds_le (q : Nat) (hq : 0 < q) :
    3 ^ gapRounds q ≤ 27 * q ^ 5 := by
  have hlog := Nat.pow_log_le_self 2 (Nat.ne_of_gt hq)
  have hp : 27 ^ Nat.log 2 q ≤ 32 ^ Nat.log 2 q :=
    Nat.pow_le_pow_left (by decide) _
  have heq : 32 ^ Nat.log 2 q = (2 ^ Nat.log 2 q) ^ 5 := by
    rw [← pow_mul, Nat.mul_comm]
    exact (pow_mul 2 5 (Nat.log 2 q)).symm
  rw [heq] at hp
  have hs := hp.trans (Nat.pow_le_pow_left hlog 5)
  dsimp [gapRounds]
  rw [pow_mul, show (3 : Nat) ^ 3 = 27 by norm_num, pow_succ]
  nlinarith

end ShiQMACenteredGap

#print axioms ShiQMACenteredGap.biasIter_gapRounds
#print axioms ShiQMACenteredGap.copies_gapRounds_le
