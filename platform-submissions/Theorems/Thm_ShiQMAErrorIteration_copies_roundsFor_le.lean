import Definitions.Def_ShiQMAErrorIteration

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.copies_roundsFor_le (m : Nat) (hm : 0 < m) : 3 ^ roundsFor m ≤ 81 * m ^ 2 := by sorry
