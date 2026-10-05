import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_biasStep_ge
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    {r s : Nat} (hrs : r ≤ s) : biasIter d r ≤ biasIter d s := by
  apply monotone_nat_of_le_succ _ hrs
  intro k
  exact biasStep_ge (biasIter_bounds hd₀ hd₁ k).1 (biasIter_bounds hd₀ hd₁ k).2
