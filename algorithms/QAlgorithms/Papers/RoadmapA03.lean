import QAlgorithms.Defs.RankOneAmplitudeSequence

namespace QAlgorithms.Papers.RoadmapA03

universe u

/-- Martyn, Rossi, Tan and Chuang, *A Grand Unification of Quantum Algorithms*,
arXiv:2105.02859v5, Theorem 2 (Amplitude Amplification), PDF/printed p.5, Eq. (13),
with the standing conventions of Section II B (p.4) and the polynomial conditions
of Theorem 1 (pp.3–4). For an odd length `d = 2 * l + 1` and real phases,
the same complex polynomial transforms every real nonzero rank-one amplitude.
The complementary polynomial carries the full degree, parity and normalization
conditions. The exact positive-sign rank-one shifts and increasing, left-to-right
product order are those of `RankOneAA.sequence`; no ambient Hermiticity is assumed.
-/
theorem amplitudeAmplification_polynomial (l : ℕ) (phi : Fin (2 * l + 1) → ℝ) :
    ∃ P Q : Polynomial ℂ,
      P.natDegree ≤ 2 * l + 1 ∧
      Q.natDegree ≤ 2 * l ∧
      HasParity P (2 * l + 1) ∧
      HasParity Q (2 * l) ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1) ∧
      ∀ (I : Type u) [Fintype I] [DecidableEq I]
        (A0 B0 : EuclideanSpace ℂ I) (hA : IsState A0) (hB : IsState B0)
        (U : Matrix.unitaryGroup I ℂ) (a : ℝ),
        a ≠ 0 → inner ℂ A0 (act (U : Matrix I I ℂ) B0) = (a : ℂ) →
        inner ℂ A0 (act (RankOneAA.sequence A0 B0 hA hB U l phi) B0) =
          P.eval (a : ℂ) := by sorry

end QAlgorithms.Papers.RoadmapA03
