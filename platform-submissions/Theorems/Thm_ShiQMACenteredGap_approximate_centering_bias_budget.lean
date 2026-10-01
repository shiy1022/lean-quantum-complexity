import Definitions.Def_ShiQMACenteredGapScalarCentering
import Theorems.Thm_ShiQMACenteredGap_approximate_centering
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.approximate_centering_bias_budget {a b u : ℝ} (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hab : b ≤ a) (q : Nat)
    (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    let d := (a - b) / 8
    0 ≤ d ∧ d ≤ 1 / 2 ∧ (1 / 6 : ℝ) ≤ (2 * q : Nat) * d ∧
    (∀ t : ℝ, a ≤ t → 1 / 2 + d ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - d) := by
  sorry
