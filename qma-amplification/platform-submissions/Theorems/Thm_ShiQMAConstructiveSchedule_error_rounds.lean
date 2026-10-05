import Definitions.Def_ShiQMAConstructiveSchedule
import Theorems.Thm_ShiQMAErrorIteration_dyadic_error_bound
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem ShiQMAConstructiveSchedule.error_rounds (p : Polynomial ℕ) (n : ℕ) :
    error (rounds p n) ≤ ((1 : ℝ) / 2) ^ (p.eval n) := by sorry
