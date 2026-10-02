import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMAConstructiveSchedule_copies_rounds_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.copies_generalGapRounds_le (q p : Polynomial ℕ) (n : Nat) :
    3 ^ generalGapRounds q p n ≤
      (3 ^ (Nat.log 2 (q.eval 1 + 1) + q.natDegree + 4) *
        (n + 1) ^ (2 * q.natDegree)) ^ 3 *
      (3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree)) := by sorry
