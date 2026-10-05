import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_centeringNumerator_value

set_option autoImplicit false

theorem ShiQMACenteredGap.centering_from_bits {a b : ℝ} (as bs : List Bool) (hlen : as.length = bs.length)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ as.length)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ as.length) :
    let j := centeringNumerator as.length (binaryNumerator as) (binaryNumerator bs)
    |(j : ℝ) / (2 : ℝ) ^ (as.length + 1) - centeringCoin a b| ≤
      1 / (2 : ℝ) ^ as.length := by
  sorry
