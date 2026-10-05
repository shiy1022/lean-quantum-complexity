import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

theorem solution {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (k : Nat) :
    ∃ j : Nat, j ≤ 2 ^ k ∧
      |(j : ℝ) / (2 : ℝ) ^ k - u| < 1 / (2 : ℝ) ^ k := by
  let j := Nat.floor (u * (2 : ℝ) ^ k)
  have hN : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) _
  have hfloor : (j : ℝ) ≤ u * (2 : ℝ) ^ k := Nat.floor_le (mul_nonneg hu₀ hN.le)
  have hlt : u * (2 : ℝ) ^ k < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj : (j : ℝ) ≤ (2 : ℝ) ^ k :=
    hfloor.trans (by nlinarith)
  refine ⟨j, by exact_mod_cast hj, ?_⟩
  have hquot : (j : ℝ) / (2 : ℝ) ^ k ≤ u := (div_le_iff₀ hN).mpr hfloor
  rw [abs_of_nonpos (sub_nonpos.mpr hquot)]
  apply (lt_div_iff₀ hN).mpr
  have hcancel := div_mul_cancel₀ (j : ℝ) (ne_of_gt hN)
  nlinarith
