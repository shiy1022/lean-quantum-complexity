import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_biasIter_dyadic
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.normalizationRounds_suffice {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (normalizationRounds q n) := by sorry
