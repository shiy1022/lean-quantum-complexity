import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_centering_from_bits

set_option autoImplicit false

theorem ShiQMACenteredGap.centering_from_bits_gap {a b : ℝ} (hab : b ≤ a)
    (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (as bs : List Bool) (haLen : as.length = coinBits q) (hbLen : bs.length = coinBits q)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ coinBits q)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ coinBits q) :
    let j := centeringNumerator (coinBits q) (binaryNumerator as) (binaryNumerator bs)
    j ≤ 2 ^ (coinBits q + 1) ∧
      |(j : ℝ) / (2 : ℝ) ^ (coinBits q + 1) - centeringCoin a b| ≤ (a - b) / 4 := by
  sorry
