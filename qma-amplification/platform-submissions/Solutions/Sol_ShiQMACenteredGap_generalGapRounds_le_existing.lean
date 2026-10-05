import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_affine_schedule_le_rounds
import Theorems.Thm_ShiQMACenteredGap_generalGapRounds_controller_form

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n ≤ rounds (gapPolynomial q p) n := by
  rw [generalGapRounds_controller_form]
  exact affine_schedule_le_rounds _ _ _
