import Definitions.Def_ShiQMACenteredGapScalarCentering
import Theorems.Thm_ShiQMACenteredGap_exists_dyadic_coin
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.exists_dyadic_centering {a b : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hab : b ≤ a) (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b)) :
    ∃ j : Nat, j ≤ 2 ^ coinBits q ∧
      |(j : ℝ) / (2 : ℝ) ^ coinBits q - centeringCoin a b| ≤ (a - b) / 4 := by
  sorry
