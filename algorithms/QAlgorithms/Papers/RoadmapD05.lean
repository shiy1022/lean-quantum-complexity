import QAlgorithms.Defs.PrimeFieldDQIMoments

noncomputable section

namespace QAlgorithms.Papers.RoadmapD05

/-- Theorem 3 (Moments of the DQI distribution), arXiv:2607.28120v1,
PDF/printed page 19, Appendix B, Eq. (B60); proof on page 20, Eqs. (B61)--(B62).
The standing assumptions are from pages 2--3 and 13: a prime field, equally sized
satisfaction sets with `r < p`, a real polynomial of degree `ell`, and normalized
amplitudes `P(f(x))`. The signed objective is the frozen `linsatObjective`.
The coefficients on the right are those of the computed square `P ^ 2`.
The distance is computed from the code `ker B.transpose`; its value is infinity
for the zero-only code, agreeing with the proof's absence-of-nonzero-codewords
criterion. The moment range remains strict, as printed in (B60).
-/
theorem dqiDistribution_moments
    {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r ell k : ℕ)
    (hr : r < p) (hF : ∀ i, (F i).card = r)
    (P : Polynomial ℝ) (hdegree : P.natDegree = ell)
    (hnormalized : ∑ x : Fin n → ZMod p,
      (P.eval (linsatObjective B F x : ℝ)) ^ 2 = 1)
    (hdecode : (2 * ell + 1 : ℕ∞) ≤
      FieldCodes.minimumDistance (FieldCodes.dualOfEncoder B))
    (hmoment : (k + 2 * ell : ℕ∞) <
      FieldCodes.minimumDistance (FieldCodes.dualOfEncoder B)) :
    ∑ x : Fin n → ZMod p,
      PrimeFieldDQI.realPolynomialWeights B F P hnormalized x *
        (linsatObjective B F x : ℝ) ^ k =
      (p : ℝ) ^ n * ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) * ((r : ℝ) / (p : ℝ)) ^ j *
          (1 - (r : ℝ) / (p : ℝ)) ^ (m - j) *
          (∑ h ∈ Finset.range (2 * ell + 1),
            (P ^ 2).coeff h * (2 * (j : ℝ) - (m : ℝ)) ^ (k + h)) := by sorry

end QAlgorithms.Papers.RoadmapD05

