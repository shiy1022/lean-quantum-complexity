import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_fractionBits_numerator

set_option autoImplicit false

theorem ShiQMACenteredGap.encodeCoin_probability (k j : Nat) (hj : j ≤ 2 ^ k) :
    (encodeCoin k j).probability = (j : ℝ) / (2 : ℝ) ^ k := by
  sorry
