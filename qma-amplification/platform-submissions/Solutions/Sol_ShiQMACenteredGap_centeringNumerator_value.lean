import Definitions.Def_ShiQMACenteredGapComputableCoin
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    (centeringNumerator k A B : ℝ) / (2 : ℝ) ^ (k + 1) =
      1 - ((A : ℝ) / (2 : ℝ) ^ k + (B : ℝ) / (2 : ℝ) ^ k) / 2 := by
  have hab : A + B ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hn : (centeringNumerator k A B : ℝ) = (2 : ℝ) ^ (k + 1) - ((A : ℝ) + B) := by
    simp only [centeringNumerator, Nat.cast_sub hab, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
  rw [hn, pow_succ]
  field_simp
  <;> ring
