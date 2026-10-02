import Definitions.Def_ShiQMACenteredGapDominatingSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.affine_schedule_le_rounds (A D n : Nat) :
    A + D * (Nat.log 2 (n + 1) + 1) ≤ rounds (schedulePolynomial A D) n := by sorry
