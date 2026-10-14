import QAlgorithms.Defs.KeylTomography
import QAlgorithms.Defs.GeneralPOVMs
import QAlgorithms.Defs.TomographyOutcomes

noncomputable section

namespace QAlgorithms.Papers.RoadmapL03

/-- O'Donnell and Wright, *Efficient quantum tomography*, arXiv:1508.01907v2,
Theorem 1.2 (PDF p.2), with the public two-stage measurement of pp.6–8.
The POVM is chosen before the unknown density matrix; its Born law is the computed
joint Schur–Weyl/Keyl law. The squared Frobenius risk is at most `(4*d-3)/n`.
Singular density matrices are included. The joint density uses (8), (9), and (11),
and the right-hand side of (10), avoiding its misplaced scalar inside the
degree-n representation on the left-hand side (PDF p.8). No change to Theorem 1.2
is made. No runtime, rank, accuracy, or normalization assumption is added. -/
theorem keyl_expectedSquaredFrobeniusError
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    ∃ measurement : Measurements.OperatorPOVM (Fin n → Fin d)
        (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ),
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho),
        Measurements.bornLaw measurement (piKron n rho)
            (Tomography.tensorDensity rho density n) =
          Tomography.keylJointLaw hd hn rho density ∧
        Tomography.keylSquaredRisk hd hn rho density ≤
          ENNReal.ofReal (((4 : ℝ) * d - 3) / n) := by sorry

end QAlgorithms.Papers.RoadmapL03
