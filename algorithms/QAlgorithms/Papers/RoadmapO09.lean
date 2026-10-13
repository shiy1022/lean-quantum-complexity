import QAlgorithms.Defs.StochasticAcceleration

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO09

open QAlgorithms.StochasticOptimization

/-- Sidford–Zhang, arXiv:2308.01582v2, Theorem 5 (PDF p.13), with Problem 1
(p.5) and Definitions 1–3 (pp.3–4): the constructed Algorithm 3 has expected
objective error at most `eps` and expected query complexity
`Otilde(d^(5/8) * (L*R/eps)^(3/2))` for the same execution.

The existential routine implements the cited mean-estimator interface of Lemma 1
(p.8); its accuracy is a conclusion, not an assumed variance-reduction theorem.
Algorithms 1 and 2 are the frozen `quantumMeanEstimationPlus` and
`quantumVarianceReduction`, including independent fresh samples and the unbounded
positive geometric level. Gaussian preparation and register reordering are known
operations, chosen before the objective and oracle. Every expanded smoothed query
counts one call to the original gradient oracle or its inverse.

The finite loop uses the ceiling of the printed real iteration budget. All other
parameters and the proximal quadratic centered at `xmd` are preserved. No
pointwise gradient bound, smoothness hypothesis or retuned precision is imposed.
The p.13/p.15 pointwise-bound assertion does not follow from Definition 2; Eq.(12)
has an extra `1/r`, and its subsequent gap identity has the wrong sign. Moreover,
the displayed Lemma 5 bound does not imply the claimed accuracy with the printed
constants. These are recorded proof gaps; this declaration retains the original
Theorem 5 target rather than assuming those intermediate claims.
-/
theorem quantumAcceleratedStochasticApproximation :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ (d : ℕ), 1 ≤ d →
    ∀ (H W : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W],
    ∀ (registers : GradientRegisters d H W) (sampling : SamplingRegisters d H)
      (layouts : (r : ℝ) → (hr : 0 < r) → GaussianQueryLayout d H W registers r hr),
    (∀ r hr, (layouts r hr).outputRegisters = sampling) →
    ∃ M : QuantumMeanEstimationProgram d H,
      (∀ L eta delta : ℝ, 0 < L → 0 < eta → eta ≤ L → 0 < delta → delta < 1 →
        ∀ O : QuantumSamplingOracle d H sampling,
        Integrable (fun v => v) O.distribution →
        Integrable (fun v => ‖v - ∫ w, w ∂O.distribution‖ ^ 2) O.distribution →
        (∫ v, ‖v - ∫ w, w ∂O.distribution‖ ^ 2 ∂O.distribution) ≤ L ^ 2 →
        ∃ hmean : IsMeasurableProgram O (M.program L eta delta),
          let meanLaw := executionLaw (M.program L eta delta) O hmean
          meanLaw Set.univ = 1 ∧ expectedCalls meanLaw < ⊤ ∧
          meanLaw {vq | ‖vq.1 - ∫ v, v ∂O.distribution‖ ≤ eta} ≥
            ENNReal.ofReal (1 - delta)) ∧
      ∀ L R eps : ℝ, 0 ≤ L → 0 ≤ R → 0 < eps →
      ∀ f : Vector d → ℝ, ConvexOn ℝ Set.univ f →
      ∀ O : QuantumStochasticGradientOracle d f H W registers,
      O.stochastic.IsBounded L →
      ∀ xstar : Vector d, ‖xstar‖ ≤ R → (∀ x, f xstar ≤ f x) →
      ∃ hrun : IsMeasurableProgram (samplingOracleOfUnitary sampling O.unitary)
        (acceleratedProgram M layouts L R eps),
        let law := gradientExecutionLaw (acceleratedProgram M layouts L R eps) sampling O hrun
        ExpectedOptimizationContract law f xstar eps ∧
        expectedCalls law < ⊤ ∧
        (threshold ≤ L * R / eps →
          expectedCalls law ≤ ENNReal.ofReal
            (C * (d : ℝ) ^ (5 / 8 : ℝ) * (L * R / eps) ^ (3 / 2 : ℝ) *
              max 1 (Real.log (2 + d) + |Real.log eps| + |Real.log L| + |Real.log R|) ^ p)) ∧
        ((L = 0 ∨ R = 0 ∨ L * R ≤ eps) → expectedCalls law = 0) := by sorry

end QAlgorithms.Papers.RoadmapO09

