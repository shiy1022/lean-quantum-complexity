import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.approximate_centering {a b u : ℝ}
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    (∀ t : ℝ, a ≤ t → 1 / 2 + (a - b) / 8 ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - (a - b) / 8) := by
  sorry
