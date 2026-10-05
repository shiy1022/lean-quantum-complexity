import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.biasIter_add (d : ℝ) (r s : Nat) :
    biasIter d (r + s) = biasIter (biasIter d r) s := by sorry
