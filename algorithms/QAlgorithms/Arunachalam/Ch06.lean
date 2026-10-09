import QAlgorithms.Defs.Learning

/-!
# Arunachalam, Chapter 6: Survey of quantum learning theory

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N" (PDF pages): the `(N, M)`-quantum query complexity of exact learning
(§6.4.2, Lemma 6.4.8 and Fact 6.4.9) and Aaronson's shadow tomography theorem (§6.6,
Theorem 6.6.2).
-/

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.133, Lemma 6.4.8: there is a concept class `C ⊆ {0,1}^N` with `|C| ≤ M` such
that every quantum exact learner for `C` (XOR membership oracle `QMQ(c)`, success probability
`≥ 2/3` on every `c ∈ C`, §6.3.1) makes `Ω(√((N − k + 1) k))` queries, for every `k ∈ [1, N]`
with `binom(N, k−1) + binom(N, k) ≤ M`. The constant of `Ω` is universal (chosen before `N`,
`M`); the learner may use any finite workspace (internal randomness via start state and
workspace). -/
theorem exactLearning_NM_lowerBound :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ N M : ℕ, ∃ C : Finset (Fin N → Bool), C.card ≤ M ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ N → N.choose (k - 1) + N.choose k ≤ M →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Fin N) Bool W T)
          (out : (Fin N × Bool) × W → (Fin N → Bool)),
          IsQExactLearner A out C →
            c0 * Real.sqrt ((((N - k + 1 : ℕ) : ℝ)) * (k : ℝ)) ≤ (T : ℝ) := by
  sorry

/-- Arunachalam p.134, Fact 6.4.9 (Kothari, Lemma 5): for every `N < M ≤ 2^N` there is a
Hamming-weight parameter `k ∈ [1, N]` with `k = Ω(log M / (log(N / log M) + 1))` and
`binom(N, k−1) + binom(N, k) ≤ M`. Logarithms are base 2; the constant of `Ω` is universal. The
text extraction prints the range as `N < M ≤ 2N`; the page reads `2^N`. The degenerate case
`N = 0` (forcing `M = 1`) is excluded by `1 ≤ N`: there the weight range `[1, N]` of
Lemma 6.4.8 is empty. -/
theorem exists_admissible_weight :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ N M : ℕ, 1 ≤ N → N < M → M ≤ 2 ^ N →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
        c0 * (Real.logb 2 (M : ℝ) / (Real.logb 2 ((N : ℝ) / Real.logb 2 (M : ℝ)) + 1)) ≤ (k : ℝ) ∧
        N.choose (k - 1) + N.choose k ≤ M := by
  sorry

open Classical in
/-- Arunachalam p.142, Theorem 6.6.2 (Aaronson, shadow tomography): there is a polynomial `p`
such that for every `ε, δ ∈ (0, 1]`, integers `m, d > 0` and known two-outcome measurements
`{E_i, 1 − E_i}`, `i ∈ [m]`, on `ℂ^d`, some learner using `k ≤ p(log m, log d, 1/ε, log(1/δ))`
copies of the unknown state — a measurement (POVM) on `ρ^{⊗k}` whose outcomes are labelled by
numbers `b_1, …, b_m ∈ [0, 1]` — outputs, for every `d`-dimensional density matrix `ρ`, with
probability at least `1 − δ` numbers satisfying `|Tr(E_i ρ) − b_i| ≤ ε` for all `i`. The source's
`ε, δ ∈ [0, 1]` is corrected to `(0, 1]`: at `ε = 0` or `δ = 0` the bound `poly(1/ε, log(1/δ))`
is undefined. -/
theorem shadowTomography :
    ∃ p : MvPolynomial (Fin 4) ℝ, ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 →
      ∀ m d : ℕ, 0 < m → 0 < d →
        ∀ E : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ i, IsEffect (E i)) →
          ∃ k : ℕ, (k : ℝ) ≤ MvPolynomial.eval
              ![Real.log (m : ℝ), Real.log (d : ℝ), 1 / ε, Real.log (1 / δ)] p ∧
            ∃ (O : Type) (_ : Fintype O) (Mo : O → Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)
              (b : O → Fin m → ℝ), IsPOVM Mo ∧ (∀ o i, 0 ≤ b o i ∧ b o i ≤ 1) ∧
              ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix ρ →
                povmEventProb Mo (piKron k ρ)
                  (fun o => ∀ i, |effectProb (E i) ρ - b o i| ≤ ε) ≥ 1 - δ := by
  sorry

end QAlgorithms.Arunachalam
