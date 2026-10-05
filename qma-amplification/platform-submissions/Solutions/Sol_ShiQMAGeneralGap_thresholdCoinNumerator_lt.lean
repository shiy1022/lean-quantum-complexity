import Definitions.Def_ShiQMAGeneralGapThresholdCoin
import Theorems.Thm_ShiQMAGeneralGap_thresholdCoinNumerator_spec

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAGeneralGap ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) (hb : 0 ≤ b n) (hab : b n ≤ a n)
    (hgap : (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    thresholdCoinNumerator A B q n < 2 ^ (rounds q n + 1) := by
  have hpos : 0 < a n - b n := by
    by_contra hn
    have hnonpos : a n - b n ≤ 0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (q.eval n) :
      (0 : ℝ) ≤ ↑(q.eval n)) hnonpos
    linarith
  have he := (abs_le.mp (thresholdCoinNumerator_spec A B q n hab hgap).2).2
  have hr : (thresholdCoinNumerator A B q n : ℝ) /
      (2 : ℝ) ^ (rounds q n + 1) < 1 := by
    dsimp [centeringCoin] at he
    linarith
  have hd : (0 : ℝ) < 2 ^ (rounds q n + 1) := pow_pos (by norm_num) _
  have ht := (div_lt_one hd).mp hr
  exact_mod_cast ht
