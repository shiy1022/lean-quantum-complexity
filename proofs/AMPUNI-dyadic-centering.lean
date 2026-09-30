import «AMPUNI-affine-centering»
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

namespace ShiQMACenteredGap

/-- Existence of a finite fair-bit coin approximating any probability.
The floor here is noncomputable on arbitrary reals; this lemma alone does not
supply a polynomial-time threshold algorithm. -/
theorem exists_dyadic_coin {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (k : Nat) :
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

/-- Only logarithmically many fair bits are needed at inverse-polynomial gap. -/
def coinBits (q : Nat) : Nat := Nat.log 2 (4 * q) + 1

/-- Finite-precision centering is mathematically sufficient for arbitrary thresholds. -/
theorem exists_dyadic_centering {a b : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hab : b ≤ a) (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b)) :
    ∃ j : Nat, j ≤ 2 ^ coinBits q ∧
      |(j : ℝ) / (2 : ℝ) ^ coinBits q - centeringCoin a b| ≤ (a - b) / 4 := by
  obtain ⟨hu₀, hu₁⟩ := centeringCoin_bounds ha₀ ha₁ hb₀ hb₁
  obtain ⟨j, hj, herr⟩ := exists_dyadic_coin hu₀ hu₁ (coinBits q)
  refine ⟨j, hj, herr.le.trans ?_⟩
  have hN : (0 : ℝ) < 2 ^ coinBits q := pow_pos (by norm_num) _
  have hnat : 4 * q ≤ 2 ^ coinBits q :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (4 * q))
  have hreal : 4 * (q : ℝ) ≤ (2 : ℝ) ^ coinBits q := by exact_mod_cast hnat
  apply (div_le_iff₀ hN).mpr
  have hmul := mul_nonneg (sub_nonneg.mpr hreal) (sub_nonneg.mpr hab)
  nlinarith

/-- Even enumeration of all coin outcomes has only linear overhead in the gap budget. -/
theorem coin_outcomes_le (q : Nat) (hq : 0 < q) :
    2 ^ coinBits q ≤ 8 * q := by
  have hlog := Nat.pow_log_le_self 2 (show 4 * q ≠ 0 by omega)
  dsimp [coinBits]
  rw [pow_succ]
  omega

end ShiQMACenteredGap

#print axioms ShiQMACenteredGap.exists_dyadic_centering

#print axioms ShiQMACenteredGap.coin_outcomes_le
