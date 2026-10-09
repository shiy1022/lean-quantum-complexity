import QAlgorithms.Defs.LearningHardInstances

/-!
# Learning survey, Chapter 4 (part a): query complexity of exact learning

S. Arunachalam, R. de Wolf, *A survey of quantum learning theory* (2017), §4.1, PDF pp. 8–12
("survey p.N").

Standing assumptions of §4.1 (p.8): a concept `c : {0,1}^n → {0,1}` is given by its truth table
of `N = 2^n` bits, so a concept class is `C : Finset (Qubits n → Bool)`; `γ(C)` (Def. 4.1) is
defined only for `|C| > 1`. A quantum exact learner (§3.1, p.6) queries `QMQ(c) : |x, b⟩ ↦
|x, b ⊕ c(x)⟩` (the frozen `xorOracle c`) and must output `h = c` with probability at least `2/3`
for every `c ∈ C`; a classical exact learner is a randomized decision tree over `MQ(c)`.
-/

namespace QAlgorithms.LearningSurvey

universe u

/-- **Theorem 4.3** (Servedio–Gortler; survey p.9). Let `N = 2^n`. Every quantum exact learner for
a concept class `C ⊆ {0,1}^N` makes `Ω(max{1/√γ(C), (log |C|)/n})` membership queries.
The constant `K` is absolute (chosen before `n`, `C`, the workspace and the learner). -/
theorem servedioGortler_quantum_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
      ∀ (W : Type u) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Qubits n) Bool W T)
        (out : (Qubits n × Bool) × W → (Qubits n → Bool)),
        Learning.IsQExactLearner A out C →
          K * max (1 / Real.sqrt (Learning.gammaParam C)) (Real.log (C.card : ℝ) / (n : ℝ)) ≤
            (T : ℝ) := by
  sorry

/-- **Corollary 4.4** (Servedio–Gortler; survey p.10). If a concept class `C ⊆ {0,1}^N`
(`N = 2^n`) has classical and quantum membership query complexities `D(C)` and `Q(C)`, then
`D(C) = O(n Q(C)^3)`. -/
theorem servedioGortler_classical_le_cube :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (C : Finset (Qubits n → Bool)),
      (Learning.classicalExactComplexity C : ℝ) ≤
        K * (n : ℝ) * (Learning.quantumExactComplexity C : ℝ) ^ 3 := by
  sorry

/-- **Theorem 4.5** (folklore; survey p.10). The classical `(N, M)`-query complexity of exact
learning is `Θ(min{M, N})`, for `N = 2^n` and every class size `2 ≤ M ≤ 2^N`. -/
theorem classical_NM_exact_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (n M : ℕ), 2 ≤ M → M ≤ 2 ^ (2 ^ n) →
      c₁ * (min M (2 ^ n) : ℕ) ≤ (Learning.classicalExactNM n M : ℝ) ∧
        (Learning.classicalExactNM n M : ℝ) ≤ c₂ * (min M (2 ^ n) : ℕ) := by
  sorry

/-- **Theorem 4.6** (Kothari; survey p.10). The quantum `(N, M)`-query complexity of exact
learning (`N = 2^n`) is `Θ(√M)` for `M ≤ N` and
`Θ(√(N log M / (log(N / log M) + 1)))` for `N < M ≤ 2^N` (logarithms base 2). -/
theorem kothari_quantum_NM_exact_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (n M : ℕ),
      (2 ≤ M → M ≤ 2 ^ n →
        c₁ * Real.sqrt (M : ℝ) ≤ (Learning.quantumExactNM n M : ℝ) ∧
          (Learning.quantumExactNM n M : ℝ) ≤ c₂ * Real.sqrt (M : ℝ)) ∧
      (2 ^ n < M → M ≤ 2 ^ (2 ^ n) →
        c₁ * Real.sqrt (((2 ^ n : ℕ) : ℝ) * Real.logb 2 (M : ℝ) /
            (Real.logb 2 (((2 ^ n : ℕ) : ℝ) / Real.logb 2 (M : ℝ)) + 1)) ≤
          (Learning.quantumExactNM n M : ℝ) ∧
        (Learning.quantumExactNM n M : ℝ) ≤
          c₂ * Real.sqrt (((2 ^ n : ℕ) : ℝ) * Real.logb 2 (M : ℝ) /
            (Real.logb 2 (((2 ^ n : ℕ) : ℝ) / Real.logb 2 (M : ℝ)) + 1))) := by
  sorry

/-- **Theorem 4.8** (Kothari; survey p.12). For every concept class `C ⊆ {0,1}^N` (`N = 2^n`,
`|C| ≥ 2`, the domain of `γ`), there is a quantum exact learner for `C` using
`O(√((1/γ(C)) / log(1/γ(C))) · log |C|)` quantum membership queries. The constant `K` is absolute;
the learner is chosen after `C` but before the target concept. -/
theorem kothari_quantum_exact_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → (Qubits n → Bool)),
        Learning.IsQExactLearner A out C ∧
          (T : ℝ) ≤ K * Real.sqrt ((1 / Learning.gammaParam C) /
            Real.log (1 / Learning.gammaParam C)) * Real.log (C.card : ℝ) := by
  sorry

end QAlgorithms.LearningSurvey
