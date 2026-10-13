import QAlgorithms.Defs.OptimalQLSPComplexity

/-!
# Optimal sparse-access quantum linear systems query complexity

Carlos Bravo-Prieto, Aram W. Harrow and Robin Kothari,
*An Optimal Quantum Linear Systems Algorithm*, arXiv:2609.35660v1.
The selected result is Theorem 1, equation (6), PDF page 2; its input and output
contracts are on PDF page 1 and the distinct row-location convention is on page 5.
-/

namespace QAlgorithms.Papers.RoadmapA20

/-- Theorem 1, equation (6), arXiv:2609.35660v1, PDF page 2:
the QLSP has query complexity Theta(kappa * sqrt(d) * log(1/eps)).

The frozen complexity ranges over positive dimensions N >= d and finite exact
entry encodings. For each public dimension and encoding, a solver is chosen before
every hidden invertible d-sparse complex A, nonzero b, and compatible oracle completion.
The input promises are specNorm A <= 1 and specNorm A inverse <= kappa. Both A and
its adjoint have row-location and XOR value access; matrix calls, their inverses and
controlled versions are counted, while supplied state preparation and known operations
are free. Successful reduced output may be mixed: success probability is at least 1/2
and its normalized conditional state has trace distance at most eps from the normalized
solution. Universal thresholds express the multiparameter asymptotic convention on p.2.

Source audit: p.9 equation (37) is read as a lower bound on recovery probability,
as its proof requires; the exact probability is norm(u)^2 / (norm(QT u)^2 + norm(u)^2).
No correction to Theorem 1 is needed.
-/
theorem optimalQLSP_queryComplexity :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ kappa0 : ℝ, 1 ≤ kappa0 ∧
      ∃ d0 : ℕ, 1 ≤ d0 ∧
      ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ kappa : ℝ, ∀ hkappa : 1 ≤ kappa, kappa0 ≤ kappa →
      ∀ d : ℕ, ∀ hd : 1 ≤ d, d0 ≤ d →
      ∀ eps : ℝ, ∀ heps : 0 < eps ∧ eps < 1, eps ≤ eps0 →
        ENNReal.ofReal (c * kappa * Real.sqrt (d : ℝ) * Real.log (1 / eps)) ≤
          OptimalQLSP.queryComplexity d hd kappa eps hkappa heps ∧
        OptimalQLSP.queryComplexity d hd kappa eps hkappa heps ≤
          ENNReal.ofReal (C * kappa * Real.sqrt (d : ℝ) * Real.log (1 / eps)) := by sorry

end QAlgorithms.Papers.RoadmapA20
