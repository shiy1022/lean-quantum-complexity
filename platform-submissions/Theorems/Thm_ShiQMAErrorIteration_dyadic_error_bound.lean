import Definitions.Def_ShiQMAErrorIteration
import Theorems.Thm_ShiQMAErrorIteration_scaled_error_bound

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.dyadic_error_bound (r : Nat) :
    error (r + 3) ≤ ((1 : ℝ) / 2) ^ (2 ^ r) := by sorry
