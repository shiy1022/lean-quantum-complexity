import Definitions.Def_ShiQMAVariableRoundsPolynomialFamily
import Theorems.Thm_ShiQMAErrorIteration_copies_roundsFor_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiQMAErrorIteration Polynomial ShiQMAVariableRounds

theorem solution (m : Nat) :
    3 ^ roundsFor m ≤ 81 * (m + 1) ^ 2 := by
  by_cases hm : m = 0
  · subst m
    norm_num [roundsFor]
  · have hp : 0 < m := Nat.pos_of_ne_zero hm
    calc
      3 ^ roundsFor m ≤ 81 * m ^ 2 := copies_roundsFor_le m hp
      _ ≤ 81 * (m + 1) ^ 2 := by nlinarith
