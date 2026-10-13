import QAlgorithms.Defs.NonconvexQueryContracts

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO11

open QAlgorithms.Nonconvex

/-- Zhang, Leng, Li, arXiv:2007.10253v3, Theorem 1 (informal), PDF p.4.
The original-paper existence claim is made explicit by Theorem 4, Eq.(66),
pp.18-19, the returned-point rule of Remark 2, p.20, and the accelerated
evaluation-only extension asserted after Theorem 5 and in Remark 3, p.24.
Smoothness and stationarity are those of p.2, Eq.(1); access is precisely
the clean real-value unitary interface of p.3, Eqs.(2)-(3). All oracle calls,
including inverse calls, are counted by the computed execution law.

The actual attained starting gap is public. Smoothness, confidence and gap
are fixed before the asymptotic constants; the program and its normalized
reset/start state are chosen before the objective and every compatible
oracle completion. The successful returned-point and cost event has mass
at least 1-delta. The p.1 footnote's broad poly(log(scale)) convention is
used, retaining the displayed log(n)^2 and epsilon^(-7/4) factors.
The zero-gap branch returns x0 without queries; positive-gap dimensions
and scales are asymptotic, avoiding a zero-query claim from log(1)=0.

This states the authors' ideal-oracle existence claim, not correctness of
literal Algorithm 3, a corrected construction, or an accelerated finite-
accuracy guarantee. The printed perturbation length, failure allocation,
unsquared trigger and continuum/periodic error issues are recorded in the
unit's SOURCE_AUDIT.md; no source correction is applied here. -/
theorem escapeSaddle_evaluationQueries
    (ell rho delta gap : ℝ) (hell : 0 < ell) (hrho : 0 < rho)
    (hdelta : 0 < delta ∧ delta < 1) (hgap : 0 ≤ gap) :
    ∃ C : ℝ, 0 < C ∧ ∃ degree : ℕ, ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∃ threshold : ℝ, 1 ≤ threshold ∧
      ∀ (n : ℕ) (eps : ℝ), 1 ≤ n → 0 < eps → eps ≤ ell ^ 2 / rho →
        let scale : ℝ := gap * (Real.log n) ^ 2 * eps ^ (-(7 / 4 : ℝ))
        (gap = 0 ∨ (n0 ≤ n ∧ threshold ≤ scale)) →
        ∀ x0 : Vector n,
          ∃ (w : ℕ) (zero : Register n (Fin (w + 1))) (zero_unit : ‖zero‖ = 1)
            (program : EvaluationProgram n (Fin (w + 1))),
            (gap = 0 → program = .output x0) ∧
            ∀ f : Vector n → ℝ, IsSmoothHessianLipschitz f ell rho →
            ∀ attained : ∃ x, ∀ y, f x ≤ f y,
              initialGap f attained x0 = gap →
              ∀ U : Register n (Fin (w + 1)) ≃ₗᵢ[ℂ] Register n (Fin (w + 1)),
                IsRealEvaluationOracle (0 : Fin (w + 1)) U f →
                ∃ measurable : IsEvaluationProgramMeasurable zero zero_unit U program,
                  evaluationExecutionLaw zero zero_unit U program zero zero_unit measurable
                    {xq | IsApproxSecondOrderStationary f rho eps xq.1 ∧
                      (xq.2 : ℝ) ≤ if gap = 0 then 0
                        else C * scale * max 1 (Real.log scale) ^ degree} ≥
                    ENNReal.ofReal (1 - delta) := by sorry

end QAlgorithms.Papers.RoadmapO11
