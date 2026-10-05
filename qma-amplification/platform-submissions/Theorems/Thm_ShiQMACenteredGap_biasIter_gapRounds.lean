import Definitions.Def_ShiQMACenteredGap
import Theorems.Thm_ShiQMACenteredGap_biasIter_growth

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

theorem ShiQMACenteredGap.biasIter_gapRounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Nat) (hgap : (1 / 6 : ℝ) ≤ (q : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (gapRounds q) := by sorry
