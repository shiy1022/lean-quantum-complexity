import QAlgorithms.Defs.DiscreteAdiabaticTransport

noncomputable section

namespace QAlgorithms.Papers.RoadmapA18

open scoped NNReal

open QAlgorithms.DiscreteAdiabatic

/-- Costa, An, Sanders, Su, Babbush and Berry, arXiv:2111.08152v1,
PDF p.6 (printed p.6), Theorem 3, Eq. (15): the Second Discrete Adiabatic Theorem.
Definitions 1--2 and Eqs. (21)--(26) supply the finite differences, compatible
spectral arc windows and left polar transport. The chronological product starts
with W(0), correcting the lower index of Eq. (2) and the shifted W in Eq. (3)
as required by Theorem 15 (p.14) and its proof (p.15, Eq. (86)).
The gap adjustment is the minimum in Eq. (14), correcting the appendix's word
"maximum" (p.30). The norm is the full operator norm on a complete complex
Hilbert space. No finite-dimensional or initial-state restriction is imposed. -/
theorem secondDiscreteAdiabaticTheorem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : ℕ} (D : SpectralBandData H T)
    (c1 c2 : Fin (T + 1) → ℝ≥0)
    (firstDifference : ∀ (j : Fin (T + 1)) (valid : j.val + 1 ≤ T),
      ‖forwardDifference D.W 1 j.val valid‖ ≤ (c1 j : ℝ) / (T : ℝ))
    (secondDifference : ∀ (j : Fin (T + 1)) (valid : j.val + 2 ≤ T),
      ‖forwardDifference D.W 2 j.val valid‖ ≤ (c2 j : ℝ) / (T : ℝ) ^ 2)
    (positiveGaps : ∀ (j : Fin (T + 1)) (k : Fin 3) (valid : j.val + k.val ≤ T),
      0 < windowGap D j k valid)
    (stepSize : ∀ j : Fin (T + 1),
      4 * neighborEnvelope 1 c1 j / neighborGap D j ≤ (T : ℝ))
    (n : Fin (T + 1)) :
    let cHat1 := neighborEnvelope 1 c1
    let cHat2 := neighborEnvelope 2 c2
    let gap := neighborGap D
    ‖walkEvolution D.W n - idealEvolution D n‖ ≤
      12 * cHat1 0 / ((T : ℝ) * gap 0 ^ 2) +
      12 * cHat1 n / ((T : ℝ) * gap n ^ 2) +
      6 * cHat1 n / ((T : ℝ) * gap n) +
      305 * (∑ j ∈ Finset.Ico (1 : Fin (T + 1)) n,
        cHat1 j ^ 2 / ((T : ℝ) ^ 2 * gap j ^ 3)) +
      44 * (∑ j ∈ Finset.Ico (0 : Fin (T + 1)) n,
        cHat1 j ^ 2 / ((T : ℝ) ^ 2 * gap j ^ 2)) +
      32 * (∑ j ∈ Finset.Ico (1 : Fin (T + 1)) n,
        cHat2 j / ((T : ℝ) ^ 2 * gap j ^ 2)) := by sorry

end QAlgorithms.Papers.RoadmapA18
