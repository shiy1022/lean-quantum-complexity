import Definitions.Def_ShiQMAErrorIteration

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.scaled_error_bound (r : Nat) :
    3 * error (r + 1) ≤ ((7 : ℝ) / 9) ^ (2 ^ r) := by sorry
