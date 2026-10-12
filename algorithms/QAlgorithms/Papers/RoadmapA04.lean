import QAlgorithms.Defs.GeneralizedQSP

namespace QAlgorithms.Papers.RoadmapA04

/-- Motlagh and Wiebe, *Generalized Quantum Signal Processing*, arXiv:2308.01501v2,
Theorem 3, equation (7), PDF p.4 (signal and rotation: equations (5)--(6), PDF p.3).
For prescribed complex polynomials, exact first-column realization by one set of real angles
for every finite-dimensional unitary is equivalent to the degree bounds and normalization
on the entire unit circle. The sequence is R_d A ... R_1 A R_0, with A = diag(U,I).
Equation (6), rather than the reverse-proof base-case prose typo, fixes Q = exp(i lambda) sin theta.
The printed rotations are unitary; no determinant-one condition or phase adjustment is imposed. -/
theorem generalizedQSP_iff (d : ℕ) (P Q : Polynomial ℂ) :
    (∃ theta phi : Fin (d + 1) → ℝ, ∃ lam : ℝ,
      ∀ N : ℕ, 0 < N → ∀ U : Matrix (Fin N) (Fin N) ℂ,
        U ∈ Matrix.unitaryGroup (Fin N) ℂ → ∀ i j : Fin N,
          gqspSequence theta phi lam U (false, i) (false, j) =
            (Polynomial.aeval U P) i j ∧
          gqspSequence theta phi lam U (true, i) (false, j) =
            (Polynomial.aeval U Q) i j) ↔
      P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by sorry

end QAlgorithms.Papers.RoadmapA04
