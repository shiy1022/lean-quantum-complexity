import QAlgorithms.Defs.ClassicalShadowPrediction

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL01

open QAlgorithms.ClassicalShadows

/-- Huang, Kueng and Preskill, arXiv:2002.08953v2, supplementary Theorem 1,
PDF p.13, Eqs. (S13)--(S14). Primitive and snapshots: p.11, Eqs. (S1)--(S3);
shadow norm and median of means: p.12, Eqs. (S7), (S12).
The queued p.3 locator is the informal version, continuing on p.4.

The printed zero endpoints for eps and delta make (S13) undefined and are excluded;
the upper endpoints are retained. The frozen sampleSchedule rounds K and N upward
and takes N at least one, including when every centered observable is zero.
Positivity witnesses are conclusions, not additional assumptions. The K-by-N array
uses exactly K*N independent copies. For even K the frozen lower median fixes the
source's unspecified tie convention. Completeness means invertibility of the
averaged channel, including for continuous or nonuniform ensembles.
No unbiasedness, variance bound, or snapshot trace property is assumed. -/
theorem classicalShadow_prediction
    {n M : ℕ} (P : MeasurementPrimitive n)
    (O : Fin M → Space n) (hO : ∀ i, (O i).IsHermitian) (hM : 0 < M)
    (rho : Space n) (hrho : IsDensityMatrix rho)
    (eps delta : ℝ) (heps : 0 < eps ∧ eps ≤ 1) (hdelta : 0 < delta ∧ delta ≤ 1) :
    let counts := sampleSchedule P O hO hM eps delta heps hdelta
    ∃ (hK : 0 < counts.1) (hN : 0 < counts.2),
      ENNReal.ofReal (1 - delta) ≤
        arrayLaw P rho hrho counts.1 counts.2
          {shots | ∀ i : Fin M,
            |medianOfMeans P (O i) counts.1 counts.2 hK hN shots -
              ((O i) * rho).trace.re| ≤ eps} := by sorry

end QAlgorithms.Papers.RoadmapL01
