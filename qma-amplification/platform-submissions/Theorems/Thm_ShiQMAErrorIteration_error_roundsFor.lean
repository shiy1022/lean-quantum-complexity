import Definitions.Def_ShiQMAErrorIteration
import Theorems.Thm_ShiQMAErrorIteration_dyadic_error_bound

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.error_roundsFor (m : Nat) : error (roundsFor m) ≤ ((1 : ℝ) / 2) ^ m := by sorry
