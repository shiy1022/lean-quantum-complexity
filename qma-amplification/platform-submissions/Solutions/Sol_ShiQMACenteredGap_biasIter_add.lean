import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution (d : ℝ) (r s : Nat) :
    biasIter d (r + s) = biasIter (biasIter d r) s := by
  induction s with
  | zero => rfl
  | succ s ih => exact congrArg biasStep ih
