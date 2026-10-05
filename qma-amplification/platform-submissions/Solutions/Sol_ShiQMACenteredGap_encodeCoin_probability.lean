import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_fractionBits_numerator
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution (k j : Nat) (hj : j ≤ 2 ^ k) :
    (encodeCoin k j).probability = (j : ℝ) / (2 : ℝ) ^ k := by
  by_cases h : j = 2 ^ k
  · subst j
    simp [encodeCoin, CoinCode.probability]
  · simp [encodeCoin, h, CoinCode.probability, dyadicValue,
      fractionBits_length, fractionBits_numerator k j (by omega)]
