import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace ShiQMACenteredGap

/-- An ordinary executable conversion from binary fractional bits to a natural numerator. -/
def binaryNumerator : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + binaryNumerator bs

noncomputable def dyadicValue (bs : List Bool) : ℝ :=
  (binaryNumerator bs : ℝ) / (2 : ℝ) ^ bs.length

theorem binaryNumerator_lt (bs : List Bool) : binaryNumerator bs < 2 ^ bs.length := by
  induction bs with
  | nil => norm_num [binaryNumerator]
  | cons b bs ih =>
    cases b <;> simp only [binaryNumerator, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, pow_succ, zero_add] <;> omega

theorem dyadicValue_bounds (bs : List Bool) : 0 ≤ dyadicValue bs ∧ dyadicValue bs ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ bs.length := pow_pos (by norm_num) _
  have hb : (binaryNumerator bs : ℝ) ≤ (2 : ℝ) ^ bs.length := by
    exact_mod_cast (binaryNumerator_lt bs).le
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hpos.le
  · exact (div_le_one hpos).mpr hb

/-- Numerator of the centering coin, obtained by finite integer arithmetic on
threshold approximations. A numerator equal to the denominator means the constant-one coin. -/
def centeringNumerator (k A B : Nat) : Nat := 2 ^ (k + 1) - (A + B)

theorem centeringNumerator_le (k A B : Nat) : centeringNumerator k A B ≤ 2 ^ (k + 1) :=
  Nat.sub_le _ _

/-- Executable fixed-width binary encoder for the fractional coin circuit. -/
def fractionBits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, j => decide (2 ^ k ≤ j) :: fractionBits k (j % 2 ^ k)

theorem fractionBits_length (k j : Nat) : (fractionBits k j).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [fractionBits, ih]

/-- A dyadic code also handles the exact probability one without rounding it down. -/
inductive CoinCode where
  | certainOne
  | fractional (bits : List Bool)
  deriving DecidableEq, Repr

noncomputable def CoinCode.probability : CoinCode → ℝ
  | .certainOne => 1
  | .fractional bs => dyadicValue bs

def encodeCoin (k j : Nat) : CoinCode :=
  if j = 2 ^ k then .certainOne else .fractional (fractionBits k j)

end ShiQMACenteredGap
