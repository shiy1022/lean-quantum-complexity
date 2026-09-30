import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

theorem ShiQMACenteredGap.copies_gapRounds_le (q : Nat) (hq : 0 < q) :
    3 ^ gapRounds q ≤ 27 * q ^ 5 := by sorry
