import Definitions.Def_ShiQMAGeneralGapThresholdCoin
import Theorems.Thm_ShiQMAGeneralGap_thresholdCoinNumerator_lt
import Theorems.Thm_ShiQMAGeneralGap_thresholdCoinNumerator_spec
import Theorems.Thm_ShiQMACenteredGap_fractionBits_numerator

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAGeneralGap ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) (hb : 0 ≤ b n) (hab : b n ≤ a n)
    (hgap : (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    |dyadicValue (thresholdCoinBits A B q n) - centeringCoin (a n) (b n)| ≤
      (a n - b n) / 4 := by
  have hj := thresholdCoinNumerator_lt A B q n hb hab hgap
  simpa only [thresholdCoinBits, dyadicValue, fractionBits_length,
    fractionBits_numerator _ _ hj] using
    (thresholdCoinNumerator_spec A B q n hab hgap).2
