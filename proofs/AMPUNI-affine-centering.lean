import «AMPUNI-centered-gap»

set_option autoImplicit false

namespace ShiQMACenteredGap

/-- The probability of the auxiliary coin used in affine acceptance centering. -/
noncomputable def centeringCoin (a b : ℝ) : ℝ := 1 - (a + b) / 2

/-- Run the verifier with probability one half, otherwise use the auxiliary coin.
This definition is scalar arithmetic, not yet a circuit implementation. -/
noncomputable def centeredAcceptance (u t : ℝ) : ℝ := (t + u) / 2

theorem centeringCoin_bounds {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    0 ≤ centeringCoin a b ∧ centeringCoin a b ≤ 1 := by
  dsimp [centeringCoin]
  constructor <;> linarith

theorem centeredAcceptance_bounds {u t : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ centeredAcceptance u t ∧ centeredAcceptance u t ≤ 1 := by
  dsimp [centeredAcceptance]
  constructor <;> linarith

theorem centeredAcceptance_mono {u t t' : ℝ} (h : t ≤ t') :
    centeredAcceptance u t ≤ centeredAcceptance u t' := by
  dsimp [centeredAcceptance]
  linarith

theorem exact_centering (a b : ℝ) :
    centeredAcceptance (centeringCoin a b) a = 1 / 2 + (a - b) / 4 ∧
    centeredAcceptance (centeringCoin a b) b = 1 / 2 - (a - b) / 4 := by
  dsimp [centeringCoin, centeredAcceptance]
  constructor <;> ring

/-- An approximation error of at most a quarter of the original gap retains
at least one eighth of that gap as a bias on each side of one half. -/
theorem approximate_centering {a b u : ℝ}
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    (∀ t : ℝ, a ≤ t → 1 / 2 + (a - b) / 8 ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - (a - b) / 8) := by
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  dsimp [centeringCoin] at hl hr
  constructor
  · intro t ht
    dsimp [centeredAcceptance]
    linarith
  · intro t ht
    dsimp [centeredAcceptance]
    linarith

/-- Quantitative connection from an inverse gap to the normalization schedule.
The hypothesis is a bound on the scalar coin approximation, not a uniformity assumption. -/
theorem approximate_centering_bias_budget {a b u : ℝ} (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hab : b ≤ a) (q : Nat)
    (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    let d := (a - b) / 8
    0 ≤ d ∧ d ≤ 1 / 2 ∧ (1 / 6 : ℝ) ≤ (2 * q : Nat) * d ∧
    (∀ t : ℝ, a ≤ t → 1 / 2 + d ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - d) := by
  dsimp only
  refine ⟨by linarith, by linarith, ?_, (approximate_centering hu).1,
    (approximate_centering hu).2⟩
  push_cast
  nlinarith

end ShiQMACenteredGap

#print axioms ShiQMACenteredGap.approximate_centering
#print axioms ShiQMACenteredGap.approximate_centering_bias_budget
