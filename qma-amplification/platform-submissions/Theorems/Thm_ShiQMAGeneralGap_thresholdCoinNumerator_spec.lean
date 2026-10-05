import Definitions.Def_ShiQMAGeneralGapThresholdCoin
import Theorems.Thm_ShiQMACenteredGap_centering_from_bits
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAGeneralGap ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMAGeneralGap.thresholdCoinNumerator_spec {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) (hab : b n ≤ a n)
    (hgap : (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    thresholdCoinNumerator A B q n ≤ 2 ^ (rounds q n + 1) ∧
    |(thresholdCoinNumerator A B q n : ℝ) / (2 : ℝ) ^ (rounds q n + 1) -
      centeringCoin (a n) (b n)| ≤ (a n - b n) / 4 := by sorry
