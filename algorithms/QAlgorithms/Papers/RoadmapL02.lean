import QAlgorithms.Defs.ContinuousPOVMDensities
import QAlgorithms.Defs.TomographyOutcomes
import QAlgorithms.Defs.SchurTomography
import QAlgorithms.Defs.QuantumInformation

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL02

/-- Haah, Harrow, Ji, Wu and Yu, *Sample-optimal tomography of quantum states*,
arXiv:1508.01797v2, PDF p.6, Section V, equations (10) and (14).
For positive qudit dimension and copy count, the equation-(10) continuous collective
POVM exists independently of the unknown state. Its reference is counting measure on
partitions times normalized Haar measure on U(d); its output is U lambdaBar U adjoint.
For every normalized positive semidefinite input, the infidelity tail has the printed
finite-copy bound with the input's actual rank. Fidelity is unsquared. The implicit
physical threshold domain is the closed interval [0,1], including its two endpoints. -/
theorem collectivePOVM_fidelityTail (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∃ M : Measurements.DensityPOVM (Fin n → Fin d)
        (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ),
      M.reference = Measure.count.prod (Schur.unitaryHaar d) ∧
      (∀ outcome, M.density outcome =
        Tomography.haahDensity hd hn outcome.1 outcome.2) ∧
      (∀ outcome : Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ,
        IsDensityMatrix (Schur.estimate hd hn outcome.1 outcome.2)) ∧
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho),
        let law := Measurements.bornLaw (Measurements.densityOperatorPOVM M)
          (piKron n rho) (Tomography.tensorDensity rho hrho n)
        IsProbabilityMeasure law ∧
        law = Tomography.haahJointLaw hd hn rho hrho ∧
        ∀ delta : ℝ, 0 ≤ delta → delta ≤ 1 →
          law {outcome | rootFidelity (Schur.estimate hd hn outcome.1 outcome.2) rho ≤
            1 - delta} ≤
            ENNReal.ofReal (((n : ℝ) + 1) ^ (3 * d * rho.rank) *
              Real.exp (-2 * (n : ℝ) * delta)) := by sorry

end QAlgorithms.Papers.RoadmapL02
