import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

theorem ShiQMACenteredGap.biasIter_bounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    0 ≤ biasIter d r ∧ biasIter d r ≤ 1 / 2 := by sorry
