import Definitions.Def_ShiQMACenteredGap
import Theorems.Thm_ShiQMACenteredGap_biasIter_growth

set_option autoImplicit false

/-- Three majority rounds suffice for each factor of two in the initial inverse bias. -/
theorem ShiQMACenteredGap.biasIter_dyadic {d : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) ((2 : ℝ) ^ r * d) ≤
      ShiQMACenteredGap.biasIter d (3 * r) := by
  sorry
