import Definitions.Def_ShiQMAGeneralGapThresholdCoin
import Theorems.Thm_ShiQMAConstructiveSchedule_copies_rounds_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAGeneralGap ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) :
    thresholdCoinNumerator A B q n ≤
      2 * (3 ^ (Nat.log 2 (q.eval 1 + 1) + q.natDegree + 4) *
        (n + 1) ^ (2 * q.natDegree)) := by
  have hnum : thresholdCoinNumerator A B q n ≤ 2 ^ (rounds q n + 1) :=
    centeringNumerator_le _ _ _
  have hp : 2 ^ rounds q n ≤ 3 ^ rounds q n := Nat.pow_le_pow_left (by decide) _
  have hb := copies_rounds_le q n
  rw [pow_succ] at hnum
  nlinarith
