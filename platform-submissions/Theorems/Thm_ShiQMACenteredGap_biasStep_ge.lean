import Definitions.Def_ShiQMACenteredGapDominatingSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.biasStep_ge {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2) : d ≤ biasStep d := by sorry
