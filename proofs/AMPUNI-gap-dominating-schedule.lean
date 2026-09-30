import «AMPUNI-general-gap-schedule»
import Mathlib.Algebra.Polynomial.Degree.Operations

set_option autoImplicit false

namespace ShiQMACenteredGap
open ShiQMAConstructiveSchedule

/-- Encode any fixed affine-logarithmic round budget into the polynomial
parameter of the already implemented generator. -/
noncomputable def schedulePolynomial (A D : Nat) : Polynomial ℕ :=
  Polynomial.monomial D (2 ^ A)

theorem affine_schedule_le_rounds (A D n : Nat) :
    A + D * (Nat.log 2 (n + 1) + 1) ≤ rounds (schedulePolynomial A D) n := by
  have hd : (schedulePolynomial A D).natDegree = D := by
    exact Polynomial.natDegree_monomial_eq D (pow_ne_zero _ (by decide))
  have he : (schedulePolynomial A D).eval 1 = 2 ^ A := by
    simp [schedulePolynomial]
  have hl : A ≤ Nat.log 2 (2 ^ A + 1) :=
    Nat.le_log_of_pow_le (by decide) (Nat.le_succ _)
  dsimp [rounds, exponentBudget]
  rw [hd, he]
  omega

noncomputable def gapPolynomial (q p : Polynomial ℕ) : Polynomial ℕ :=
  schedulePolynomial
    (3 * (Nat.log 2 (q.eval 1 + 1) + 4) + Nat.log 2 (p.eval 1 + 1) + 4)
    (3 * q.natDegree + p.natDegree)

theorem generalGapRounds_le_existing (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n ≤ rounds (gapPolynomial q p) n := by
  rw [generalGapRounds_controller_form]
  exact affine_schedule_le_rounds _ _ _

/-- Bias never decreases under a majority round on the upper half interval. -/
theorem biasStep_ge {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2) : d ≤ biasStep d := by
  have hs : 0 ≤ 1 / 2 - 2 * d ^ 2 := by nlinarith
  have h := mul_nonneg hd₀ hs
  dsimp [biasStep]
  nlinarith

theorem biasIter_rounds_mono {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    {r s : Nat} (hrs : r ≤ s) : biasIter d r ≤ biasIter d s := by
  apply monotone_nat_of_le_succ _ hrs
  intro k
  exact biasStep_ge (biasIter_bounds hd₀ hd₁ k).1 (biasIter_bounds hd₀ hd₁ k).2

/-- The existing concrete generator's schedule is sufficient for centered gaps. -/
theorem existing_rounds_suffice {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    (q p : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    1 / 2 - ((1 : ℝ) / 2) ^ (p.eval n) ≤
      biasIter d (rounds (gapPolynomial q p) n) :=
  (generalGapRounds_suffice hd₀ hd₁ q p n hgap).trans
    (biasIter_rounds_mono hd₀ hd₁ (generalGapRounds_le_existing q p n))

end ShiQMACenteredGap

#print axioms ShiQMACenteredGap.existing_rounds_suffice
