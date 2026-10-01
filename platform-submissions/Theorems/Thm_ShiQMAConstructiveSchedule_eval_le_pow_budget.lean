import Definitions.Def_ShiQMAConstructiveSchedule
import Theorems.Thm_ShiQMAPolynomialBound_eval_le_coeffSum_mul

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem ShiQMAConstructiveSchedule.eval_le_pow_budget (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ 2 ^ exponentBudget p n := by sorry
