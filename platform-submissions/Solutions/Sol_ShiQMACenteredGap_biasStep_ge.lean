import Definitions.Def_ShiQMACenteredGapDominatingSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2) : d ≤ biasStep d := by
  have hs : 0 ≤ 1 / 2 - 2 * d ^ 2 := by nlinarith
  have h := mul_nonneg hd₀ hs
  dsimp [biasStep]
  nlinarith
