import Definitions.Def_ShiQMAVariableRoundsPolynomialFamily
import Theorems.Thm_ShiQMAErrorIteration_copies_roundsFor_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiQMAErrorIteration Polynomial ShiQMAVariableRounds

theorem ShiQMAVariableRounds.copies_roundsFor_le_all (m : Nat) :
    3 ^ roundsFor m ≤ 81 * (m + 1) ^ 2 := by sorry
