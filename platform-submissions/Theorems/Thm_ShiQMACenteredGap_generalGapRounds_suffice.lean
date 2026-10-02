import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_normalizationRounds_suffice
import Theorems.Thm_ShiQMACenteredGap_biasIter_mono
import Theorems.Thm_ShiQMACenteredGap_biasIter_add
import Theorems.Thm_ShiQMACenteredGap_biasIter_standard
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds
import Theorems.Thm_ShiQMAConstructiveSchedule_error_rounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.generalGapRounds_suffice {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q p : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    1 / 2 - ((1 : ℝ) / 2) ^ (p.eval n) ≤ biasIter d (generalGapRounds q p n) := by sorry
