import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution {a b u : ℝ}
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    (∀ t : ℝ, a ≤ t → 1 / 2 + (a - b) / 8 ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - (a - b) / 8) := by
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  dsimp [centeringCoin] at hl hr
  constructor
  · intro t ht
    dsimp [centeredAcceptance]
    linarith
  · intro t ht
    dsimp [centeredAcceptance]
    linarith
