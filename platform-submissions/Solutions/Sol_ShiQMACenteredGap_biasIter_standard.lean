import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMACenteredGap ShiQMAErrorIteration

theorem solution (r : Nat) :
    biasIter (1 / 6) r = 1 / 2 - error r := by
  induction r with
  | zero => norm_num [biasIter, error]
  | succ r ih =>
    simp only [biasIter, ih, error, biasStep, majorityError]
    ring
