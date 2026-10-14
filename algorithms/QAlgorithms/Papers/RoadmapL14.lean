import QAlgorithms.Defs.ExactPauliRecovery

noncomputable section

open scoped ENNReal ComplexOrder

namespace QAlgorithms.Papers.RoadmapL14

/-- Gross, Liu, Flammia, Becker and Eisert, *Quantum state tomography via compressed
sensing*, arXiv:0909.3304v4, PDF p.2, Theorem 1 and convex program (1); sampling
with replacement and the Hermitian optimization domain are specified on PDF pp.5-6.
For each fixed density matrix of exact rank `r`, `m` independent uniform unphased
Pauli expectations determine the unique trace-norm minimizer, except with probability
at most `a * exp (-b * c)`, for absolute positive constants and `c >= c0`.
Here `m = ceil (c * d * r * (ln d)^2)` and `d = 2^n`. The data are exact expectations;
the objective is the full trace norm and competitors have trace one and are Hermitian,
without a positivity or rank constraint. This counts settings, not copies or runtime. -/
theorem lowRankTomography_exact :
    ∃ a b c0 : ℝ, 0 < a ∧ 0 < b ∧ 0 < c0 ∧
      ∀ (n r : ℕ) (rho : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ),
      ∀ density : QAlgorithms.IsDensityMatrix rho, rho.rank = r →
      ∀ c : ℝ, c0 ≤ c →
        let d : ℕ := 2 ^ n
        let m : ℕ := ⌈c * (d : ℝ) * (r : ℝ) * Real.log (d : ℝ) ^ 2⌉₊
        (QAlgorithms.PauliDesign.uniformDesign n m).toOuterMeasure
          {A | QAlgorithms.LowRankTomography.optimizerSet A
            (QAlgorithms.PauliDesign.expectationData A rho density.1.isHermitian) ≠ {rho}} ≤
          ENNReal.ofReal (a * Real.exp (-b * c)) := by sorry

end QAlgorithms.Papers.RoadmapL14