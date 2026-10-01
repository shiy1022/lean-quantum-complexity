import Definitions.Def_ShiQMAGeneralGapThresholdCoin
import Theorems.Thm_ShiQMACenteredGap_centering_from_bits
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAGeneralGap ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) (hab : b n ≤ a n)
    (hgap : (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    thresholdCoinNumerator A B q n ≤ 2 ^ (rounds q n + 1) ∧
    |(thresholdCoinNumerator A B q n : ℝ) / (2 : ℝ) ^ (rounds q n + 1) -
      centeringCoin (a n) (b n)| ≤ (a n - b n) / 4 := by
  let k := rounds q n
  let as := A.approximate (thresholdInput n k)
  let bs := B.approximate (thresholdInput n k)
  have hal : as.length = k := A.length_eq n k
  have hbl : bs.length = k := B.length_eq n k
  have herr := centering_from_bits as bs (hal.trans hbl.symm)
    (by simpa only [hal] using A.error_le n k)
    (by simpa only [hal] using B.error_le n k)
  rw [hal] at herr
  refine ⟨centeringNumerator_le _ _ _, herr.trans ?_⟩
  have hnat : 4 * q.eval n ≤ 2 ^ k := by
    have h := eval_le_pow_budget q n
    dsimp [k, rounds]
    rw [pow_add]
    norm_num
    omega
  have hreal : 4 * (↑(q.eval n) : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) _
  apply (div_le_iff₀ hpos).mpr
  have hm := mul_nonneg (sub_nonneg.mpr hreal) (sub_nonneg.mpr hab)
  nlinarith
