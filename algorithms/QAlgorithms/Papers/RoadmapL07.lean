import QAlgorithms.Defs.RobustShadowRetrieval

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL07

open QAlgorithms.RobustShadow

/-- Chen, Yu, Zeng and Flammia, *Robust shadow estimation*, arXiv:2011.09636v2,
PDF p.22, Theorem 7, Eqs. (B24)--(B25), for Protocol 1 (PDF pp.18--19).
One fixed CPTP noise channel acts after every uniformly sampled global Clifford;
calibration uses perfectly prepared zero states and independent identical shots.
The probability concerns one event giving a meaningful estimated inverse and the
asymptotic bias bound simultaneously for every Hermitian observable and density matrix.
Positive integer batches round the source's real parameters upward: N >= 68 A,
K >= 2 ln(2/delta), where A is the printed B24 factor. The actual count is N*K.
The printed numerator 1+eps^2 is retained. The proof's choice of gamma would instead
yield (1+eps)^2 by its variance estimate; this unresolved proof discrepancy and the
rounding convention require independent source moderation (see MODERATION_NOTES.md).
-/
theorem robustCalibration_uniformBias {n : ℕ}
    [Fintype (QAlgorithms.Clifford.ProjectiveGroup n)]
    (hn : 0 < n)
    (Lambda : Superop (Qubits n) (Qubits n)) (lawful : IsChannel Lambda)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
    (hfidelity : ((2 : ℝ) ^ n)⁻¹ < zFidelity Lambda lawful)
    (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hbatch : 68 * ((1 + eps ^ 2) * (1 + ((2 : ℝ) ^ n)⁻¹) ^ 2) /
      (eps ^ 2 * (zFidelity Lambda lawful - ((2 : ℝ) ^ n)⁻¹) ^ 2) ≤ (N : ℝ))
    (hbatches : 2 * Real.log (2 / delta) ≤ (K : ℝ)) :
    calibrationLaw hn hN hK Lambda lawful
      {record | uniformBiasEvent hn hN hK Lambda lawful eps heps record} ≥
        ENNReal.ofReal (1 - delta) := by sorry

end QAlgorithms.Papers.RoadmapL07
