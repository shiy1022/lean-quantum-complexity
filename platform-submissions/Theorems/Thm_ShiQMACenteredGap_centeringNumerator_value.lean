import Definitions.Def_ShiQMACenteredGapComputableCoin

set_option autoImplicit false

theorem ShiQMACenteredGap.centeringNumerator_value (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    (centeringNumerator k A B : ℝ) / (2 : ℝ) ^ (k + 1) =
      1 - ((A : ℝ) / (2 : ℝ) ^ k + (B : ℝ) / (2 : ℝ) ^ k) / 2 := by
  sorry
