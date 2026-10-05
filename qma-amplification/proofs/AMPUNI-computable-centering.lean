import «AMPUNI-dyadic-centering»
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

theorem centeringNumerator_value (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    (centeringNumerator k A B : ℝ) / (2 : ℝ) ^ (k + 1) =
      1 - ((A : ℝ) / (2 : ℝ) ^ k + (B : ℝ) / (2 : ℝ) ^ k) / 2 := by
  have hab : A + B ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hn : (centeringNumerator k A B : ℝ) = (2 : ℝ) ^ (k + 1) - ((A : ℝ) + B) := by
    simp only [centeringNumerator, Nat.cast_sub hab, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
  rw [hn, pow_succ]
  field_simp
  <;> ring

/-- The centering coin can be computed from approximate threshold bits, with
no real floor operation and no exact-real computation. -/
theorem centering_from_bits {a b : ℝ} (as bs : List Bool) (hlen : as.length = bs.length)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ as.length)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ as.length) :
    let j := centeringNumerator as.length (binaryNumerator as) (binaryNumerator bs)
    |(j : ℝ) / (2 : ℝ) ^ (as.length + 1) - centeringCoin a b| ≤
      1 / (2 : ℝ) ^ as.length := by
  dsimp only
  have hB : binaryNumerator bs ≤ 2 ^ as.length := by
    rw [hlen]
    exact (binaryNumerator_lt bs).le
  rw [centeringNumerator_value _ _ _ (binaryNumerator_lt as).le hB]
  have he : (binaryNumerator bs : ℝ) / (2 : ℝ) ^ as.length = dyadicValue bs := by
    rw [hlen]; rfl
  change |1 - (dyadicValue as + (binaryNumerator bs : ℝ) / (2 : ℝ) ^ as.length) / 2 -
    centeringCoin a b| ≤ _
  rw [he]
  obtain ⟨hal, har⟩ := abs_le.mp ha
  obtain ⟨hbl, hbr⟩ := abs_le.mp hb
  apply abs_le.mpr
  dsimp [centeringCoin]
  constructor <;> linarith

/-- At the logarithmic precision already selected from the gap budget, the
executable numerator meets the numerical amplifier's required tolerance. -/
theorem centering_from_bits_gap {a b : ℝ} (hab : b ≤ a)
    (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (as bs : List Bool) (haLen : as.length = coinBits q) (hbLen : bs.length = coinBits q)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ coinBits q)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ coinBits q) :
    let j := centeringNumerator (coinBits q) (binaryNumerator as) (binaryNumerator bs)
    j ≤ 2 ^ (coinBits q + 1) ∧
      |(j : ℝ) / (2 : ℝ) ^ (coinBits q + 1) - centeringCoin a b| ≤ (a - b) / 4 := by
  refine ⟨centeringNumerator_le _ _ _, ?_⟩
  have herr := centering_from_bits as bs (haLen.trans hbLen.symm)
    (by simpa [haLen] using ha) (by simpa [haLen] using hb)
  rw [haLen] at herr
  apply herr.trans
  have hpos : (0 : ℝ) < 2 ^ coinBits q := pow_pos (by norm_num) _
  have hnat : 4 * q ≤ 2 ^ coinBits q :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (4 * q))
  have hreal : 4 * (q : ℝ) ≤ (2 : ℝ) ^ coinBits q := by exact_mod_cast hnat
  apply (div_le_iff₀ hpos).mpr
  have hm := mul_nonneg (sub_nonneg.mpr hreal) (sub_nonneg.mpr hab)
  nlinarith

/-- Executable fixed-width binary encoder for the fractional coin circuit. -/
def fractionBits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, j => decide (2 ^ k ≤ j) :: fractionBits k (j % 2 ^ k)

theorem fractionBits_length (k j : Nat) : (fractionBits k j).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [fractionBits, ih]

theorem fractionBits_numerator (k j : Nat) (hj : j < 2 ^ k) :
    binaryNumerator (fractionBits k j) = j := by
  induction k generalizing j with
  | zero =>
    have hj0 : j = 0 := by simpa using hj
    subst j
    rfl
  | succ k ih =>
    have hpos : 0 < (2 : Nat) ^ k := pow_pos (by decide) _
    have hrec := ih (j % 2 ^ k) (Nat.mod_lt _ hpos)
    simp only [fractionBits, binaryNumerator, fractionBits_length, hrec]
    by_cases h : 2 ^ k ≤ j
    · simp only [h, decide_true, ↓reduceIte]
      have hj' : j < 2 ^ k * 2 := by simpa only [pow_succ] using hj
      have hsub : j - 2 ^ k < 2 ^ k := by omega
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hsub]
      omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, zero_add]
      exact Nat.mod_eq_of_lt (by omega)

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

theorem encodeCoin_probability (k j : Nat) (hj : j ≤ 2 ^ k) :
    (encodeCoin k j).probability = (j : ℝ) / (2 : ℝ) ^ k := by
  by_cases h : j = 2 ^ k
  · subst j
    simp [encodeCoin, CoinCode.probability]
  · simp [encodeCoin, h, CoinCode.probability, dyadicValue,
      fractionBits_length, fractionBits_numerator k j (by omega)]

end ShiQMACenteredGap

#print axioms ShiQMACenteredGap.centering_from_bits_gap

#print axioms ShiQMACenteredGap.encodeCoin_probability
