import QAlgorithms.Defs.LinearSystems

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms

/-- QAlgorithms.linearSystemSolution: arxiv-1511.02306v2 PDF p.3, arxiv-1909.05500v3 PDF p.3, arxiv-2609.35660v1 PDF p.1. Source domains are explicit below. -/
def linearSystemSolution {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (invertible : IsUnit A) (b : EuclideanSpace ℂ (Fin N)) (nonzero : b ≠ 0) :
    EuclideanSpace ℂ (Fin N) := normalizedVec (act A⁻¹ b)

example {N : ℕ} (hN : 0 < N) (b : EuclideanSpace ℂ (Fin N)) (hb : b ≠ 0) :
    linearSystemSolution hN 1 isUnit_one b hb = normalizedVec b := by
  simp [linearSystemSolution, act]

end QAlgorithms
