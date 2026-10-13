import QAlgorithms.Defs.AQCSchedules

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.RoadmapA12

/-- The full-register final error in An--Lin, arXiv:1909.05500v3, PDF pp.3--5,
Theorem 1, Eq.(7). The norm is the operator 2-norm, and the target is
`|0> tensor (A^{-1}b / norm(A^{-1}b))`; its density matrix removes global phase. -/
noncomputable def finalError {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ)
    (b : EuclideanSpace ℂ (Qubits n))
    (psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n)) : ℝ :=
  specNorm (pureDensity (psi 1) -
    pureDensity (tensorVec (ket false) (normalizedVec (act A⁻¹ b))))

/-- An--Lin, arXiv:1909.05500v3, Theorem 1, PDF p.5 (printed 5:5),
with the standing assumptions of pp.1,3--4 and the endpoint runtime clause.
For each fixed `1 < p < 2`, a positive constant independent of the input and runtime
bounds the final density-matrix error by `C * conditionNumber A / T`, and a positive
runtime of at most `C * conditionNumber A / eps` suffices. For `p = 1` or `p = 2`,
the sufficient runtime is `O(conditionNumber A * log(conditionNumber A) / eps)`.
The endpoint big-O is asymptotic in the condition number, with a uniform threshold
at least 2; it is not a pointwise positive-runtime bound at condition number 1.
The frozen schedule completes Eq.(6) using Eq.(5): `f(s)=s` when the condition
number is 1 and the logarithmic-limit schedule when `p=1`. Appendix D's rescaled
gap gives the same schedule. `hk` is the condition-number range required by the
frozen schedule, automatic for these nonempty positive definite matrices.
Existence of each source IVP is asserted, so the error clauses are nonvacuous. -/
theorem aqcp_finalTime_error_and_runtime :
    (∀ (p : ℝ) (hp : 1 < p), p < 2 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ) (A : Matrix (Qubits n) (Qubits n) ℂ) (hA : A.PosDef),
          specNorm A = 1 →
          ∀ (b : EuclideanSpace ℂ (Qubits n)) (hb : IsState b)
            (hk : 1 ≤ conditionNumber A),
          (∀ T : ℝ, 0 < T →
            (∃ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
              AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi) ∧
            ∀ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
              AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi →
                finalError A b psi ≤ C * conditionNumber A / T) ∧
          (∀ eps : ℝ, 0 < eps →
            ∃ T : ℝ, 0 < T ∧ T ≤ C * conditionNumber A / eps ∧
              (∃ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi) ∧
              ∀ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi →
                  finalError A b psi ≤ eps)) ∧
    (∀ (p : ℝ) (hp : 0 < p), p = 1 ∨ p = 2 →
      ∃ C : ℝ, 0 < C ∧ ∃ kappa0 : ℝ, 2 ≤ kappa0 ∧
        ∀ (n : ℕ) (A : Matrix (Qubits n) (Qubits n) ℂ) (hA : A.PosDef),
          specNorm A = 1 →
          ∀ (b : EuclideanSpace ℂ (Qubits n)) (hb : IsState b)
            (hk : 1 ≤ conditionNumber A),
          kappa0 ≤ conditionNumber A →
          ∀ eps : ℝ, 0 < eps →
            ∃ T : ℝ, 0 < T ∧
              T ≤ C * conditionNumber A * Real.log (conditionNumber A) / eps ∧
              (∃ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p hp T psi) ∧
              ∀ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p hp T psi → finalError A b psi ≤ eps) := by sorry

end QAlgorithms.Papers.RoadmapA12
