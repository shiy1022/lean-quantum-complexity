import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) : biasStep d ≤ biasStep e := by
  have hed : e * d ≤ 1 / 4 := by nlinarith [sq_nonneg (e - d)]
  have hsq : e ^ 2 + e * d + d ^ 2 ≤ 3 / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ e by linarith) (show 0 ≤ 1 / 2 - e by linarith),
      mul_nonneg hd (show 0 ≤ 1 / 2 - d by linarith)]
  have h := mul_nonneg (show 0 ≤ e - d by linarith)
    (show 0 ≤ 3 / 2 - 2 * (e ^ 2 + e * d + d ^ 2) by linarith)
  dsimp [biasStep]
  nlinarith
