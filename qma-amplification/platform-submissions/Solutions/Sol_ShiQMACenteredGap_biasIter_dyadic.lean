import Definitions.Def_ShiQMACenteredGap
import Theorems.Thm_ShiQMACenteredGap_biasIter_growth

set_option autoImplicit false
open ShiQMACenteredGap

theorem solution {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) ((2 : ℝ) ^ r * d) ≤ biasIter d (3 * r) := by
  have hp : (2 : ℝ) ^ r ≤ ((4 : ℝ) / 3) ^ (3 * r) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
  exact (min_le_min_left _ (mul_le_mul_of_nonneg_right hp hd)).trans
    (biasIter_growth hd hd' (3 * r))
