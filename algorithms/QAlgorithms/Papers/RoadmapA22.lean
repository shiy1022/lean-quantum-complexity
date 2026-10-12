import QAlgorithms.Defs.BoundedMeanEstimation

noncomputable section

namespace QAlgorithms.Papers.RoadmapA22

/-- Probability that Algorithm 1's median is within `radius` of the output mean.

Montanaro, arXiv:1504.06987v3, Algorithm 1, PDF p.8. Each fresh copy undergoes the
frozen arbitrary-`t` amplitude-estimation routine: uniform `Fin t` control, controlled
powers of `U V`, inverse positive-sign QFT, and estimate `sin (pi j / t)^2`.
The product of the single-shot laws encodes independent executions. The fixed odd
repetition count is `2 * ceil (100 * log (1 / delta)) + 1`, and `realMedian` selects
the unique middle order statistic. No success or accuracy property is assumed here. -/
def monteCarloSuccessProb (S : CoherentValueSampler) (t : ℕ) (ht : 1 ≤ t)
    (delta radius : ℝ) : ℝ :=
  open Classical in
  ∑ z : Fin (boundedMeanRepetitions delta) → Fin t,
    if |realMedian (List.ofFn fun i => Real.sin (Real.pi * (z i : ℕ) / t) ^ 2) -
        samplerMean S| ≤ radius
    then ∏ i, boundedMeanShot S t ht (z i) else 0

/-- Quantum Monte Carlo mean estimation for bounded outputs: Montanaro,
arXiv:1504.06987v3, Theorem 3, PDF pp.8-9, with Algorithm 1 on p.8 and the
standing coherent-access model of Section 2 on p.7 (also Section 1.2, pp.3-4).

`S.A` acts on `n = S.h + S.k` qubits initialized in the all-zero state; the last
`S.k` qubits determine the output through `S.value`, which lies in `[0,1]` on
every basis outcome. The unitary representation has no intermediate measurements;
access includes its inverse. The frozen construction attaches a fresh flag by the
rotation with columns `(sqrt (1-value), sqrt value)` and
`(-sqrt value, sqrt (1-value))`. Thus `psi = boundedMeanState S`,
`U = meanEstimationReflection S = 2|psi><psi| - I`, and
`V = meanFlagReflection S = I - 2P`. The control schedule is independent of the
sampler and permits every positive integer `t`, including non-powers of two.

The first two bounds count fresh copies of `S.A|0^n>` and calls to `U`, including
controlled calls, from the frozen repetition list and controlled-power schedule.
The same universal constants work for every sampler and every internal oracle
instance. `max (1, log (1/delta))` states the resource bounds for all `0<delta<1`
and is equivalent to the printed logarithmic order as `delta` tends to zero.
The last two conjuncts are the relative- and additive-error corollaries, with
positive accuracy; only the relative reciprocal requires a positive mean.

The page prints `0 <= eps <= 1`, but its reciprocal bound gives no finite-query
exact-mean claim at `eps = 0`. We retain the meaningful `0 < eps <= 1` domain
and explicitly include the zero-mean behavior: the estimator outputs zero with
probability one. The source's 'easily computable' output function is used only
to implement the value-controlled rotation; this query/copy theorem assigns no
gate-time bound to that operation, and the frozen model supplies it exactly. -/
theorem monteCarlo_boundedMean :
    ∃ C K D : ℝ, 0 < C ∧ 0 < K ∧ 0 < D ∧
      ∀ (S : CoherentValueSampler) (delta : ℝ), 0 < delta → delta < 1 →
        (((boundedMeanCopyCount delta : ℕ) : ℝ) ≤
            K * max 1 (Real.log delta⁻¹) ∧
          ∀ (t : ℕ) (ht : 1 ≤ t),
            ((boundedMeanReflectionCount t delta : ℕ) : ℝ) ≤
                K * (t : ℝ) * max 1 (Real.log delta⁻¹) ∧
              1 - delta ≤ monteCarloSuccessProb S t ht delta
                (C * (Real.sqrt (samplerMean S) / (t : ℝ) + 1 / (t : ℝ) ^ 2)) ∧
              (samplerMean S = 0 → monteCarloSuccessProb S t ht delta 0 = 1)) ∧
        (∀ eps : ℝ, 0 < eps → eps ≤ 1 → 0 < samplerMean S →
          ∃ (t : ℕ) (ht : 1 ≤ t),
            (t : ℝ) ≤ D / (eps * Real.sqrt (samplerMean S)) ∧
              1 - delta ≤ monteCarloSuccessProb S t ht delta (eps * samplerMean S)) ∧
        (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
          ∃ (t : ℕ) (ht : 1 ≤ t), (t : ℝ) ≤ D / eps ∧
            1 - delta ≤ monteCarloSuccessProb S t ht delta eps) := by sorry

end QAlgorithms.Papers.RoadmapA22
