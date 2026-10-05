import Definitions.Def_ShiQMAGeneralGapThresholdCoin
import Theorems.Thm_ShiQMAConstructiveSchedule_copies_rounds_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAGeneralGap ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMAGeneralGap.thresholdCoinNumerator_size {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) :
    thresholdCoinNumerator A B q n ≤
      2 * (3 ^ (Nat.log 2 (q.eval 1 + 1) + q.natDegree + 4) *
        (n + 1) ^ (2 * q.natDegree)) := by sorry
