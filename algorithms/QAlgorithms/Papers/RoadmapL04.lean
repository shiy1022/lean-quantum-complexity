import QAlgorithms.Defs.TomographyOutcomes
import QAlgorithms.Defs.ExtendedQuantumEntropy

/-!
# Collective tomography with quantum relative entropy loss

Flammia and O'Donnell, arXiv:2305.18519v2, Corollary 1.8 (PDF p.4).
The explicit logarithmic copy bound is given immediately after Theorem 2.34 (PDF p.12).
-/

namespace QAlgorithms.Papers.RoadmapL04

open scoped ENNReal

/-- Corollary 1.8 (arXiv:2305.18519v2, PDF p.4): collective tomography of a
`d`-dimensional density matrix of rank at most the public bound `r`, with Umegaki
relative entropy at most `eps` with probability at least .99. Natural logarithms
and the support-violation value `+infinity` are supplied by `umegakiEntropy`.
The uniform copy bound `O((r*d/eps) * log(d/eps)^2)` is the paper's explicit
counterpart on PDF p.12. The absolute small-error threshold spells out the
asymptotic regime; other positive accuracies follow by using a smaller accuracy.
The collective POVM, whose outcomes are density matrices, is chosen before `rho`.
No positivity of the smallest eigenvalue or rank constraint on the estimate is required. -/
theorem relativeEntropy_collectiveTomography :
    ∃ C : ℝ, 0 < C ∧ ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 2 ∧
      ∀ d : ℕ, 1 ≤ d → ∀ r : ℕ, 1 ≤ r → r ≤ d →
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
      ∃ n : ℕ, ∃ measurement : QAlgorithms.Tomography.CollectiveMeasurement d n,
        (n : ℝ) ≤ C * ((r : ℝ) * (d : ℝ) / eps) * (Real.log ((d : ℝ) / eps)) ^ 2 ∧
        ∀ rho : Matrix (Fin d) (Fin d) ℂ, ∀ density : IsDensityMatrix rho,
          rho.rank ≤ r →
          QAlgorithms.Tomography.collectiveOutcomeLaw measurement rho density
            {sigma | QAlgorithms.QuantumLoss.umegakiEntropy rho sigma.val density sigma.property ≤
              ENNReal.ofReal eps} ≥ ENNReal.ofReal (99 / 100 : ℝ) := by sorry

end QAlgorithms.Papers.RoadmapL04
