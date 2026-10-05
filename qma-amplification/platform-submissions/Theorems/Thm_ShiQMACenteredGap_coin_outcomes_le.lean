import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.coin_outcomes_le (q : Nat) (hq : 0 < q) :
    2 ^ coinBits q ≤ 8 * q := by
  sorry
