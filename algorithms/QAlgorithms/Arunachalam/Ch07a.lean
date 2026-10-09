import QAlgorithms.Defs.BooleanFourier

/-!
# Arunachalam, Chapter 7 (part a): preliminaries of quantum sample complexity

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N" (PDF pages), §7.3: the Barnum–Knill bound for the pretty good measurement
(Theorem 7.3.1), Fourier coefficients of `f ∘ M` (Claim 7.3.5), the maximum of `(c/√t)^t`
(Claim 7.3.6), binary-entropy estimates (Facts 7.3.7, 7.3.8) and the Helstrom bound
(Fact 7.3.9).
-/

namespace QAlgorithms.Arunachalam

/-- Arunachalam p.159–160, Theorem 7.3.1 (Barnum–Knill): for an ensemble
`E = {(p_i, |ψ_i⟩)}_{i ∈ [m]}` of `d`-dimensional pure states with `p_i ≥ 0`, `∑ p_i = 1`,
the optimal average success probability `P^opt(E) = max_M ∑ p_i ⟨ψ_i|M_i|ψ_i⟩` over
`m`-outcome POVMs and the PGM success probability `P^PGM(E) = ∑ p_i |⟨ν_i|ψ_i⟩|²`
(`|ν_i⟩ = ρ^{-1/2} √p_i |ψ_i⟩`, `ρ^{-1/2}` over the non-zero eigenvalues of
`ρ = ∑ p_i |ψ_i⟩⟨ψ_i|`) satisfy `P^opt(E)² ≤ P^PGM(E) ≤ P^opt(E)`. -/
theorem barnumKnill {m d : ℕ} (p : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℂ (Fin d))
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hψ : ∀ i, IsState (ψ i)) :
    optSuccess p ψ ^ 2 ≤ pgmSuccess p ψ ∧ pgmSuccess p ψ ≤ optSuccess p ψ := by
  sorry

/-- Arunachalam p.161, Claim 7.3.5: for `f : {0,1}^m → ℝ` and `M ∈ F₂^{m×k}`, the Fourier
coefficients of `f ∘ M` (`(f ∘ M)(z) = f(Mz)` over `F₂`) are
`\widehat{f∘M}(Q) = ∑_{S ∈ {0,1}^m : Mᵀ S = Q} \hat f(S)` for every `Q ⊆ [k]` (identified with
its indicator vector). -/
theorem fourier_comp_matrix {m k : ℕ} (f : (Fin m → ZMod 2) → ℝ)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (Q : Fin k → ZMod 2) :
    boolFourier (fun z => f (M.mulVec z)) Q =
      ∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
        boolFourier f S := by
  sorry

/-- Arunachalam p.162, Claim 7.3.6: `max {(c/√t)^t : t ∈ [1, c²]} = e^{c²/(2e)}`.

Corrected statement (trap 30): the source states it for unspecified `c`; it is false for
`c < √e` (at `c = 1` the set is `{1}`, while `e^{1/(2e)} > 1`; for `|c| < 1` the interval is
empty). The source's proof places the maximiser at `t = c²/e`, which lies in `[1, c²]` exactly
when `c² ≥ e`; we therefore assume `√e ≤ c`. -/
theorem max_c_div_sqrt_pow {c : ℝ} (hc : Real.sqrt (Real.exp 1) ≤ c) :
    IsGreatest ((fun t : ℝ => (c / Real.sqrt t) ^ t) '' Set.Icc 1 (c ^ 2))
      (Real.exp (c ^ 2 / (2 * Real.exp 1))) := by
  sorry

/-- Arunachalam p.162, Fact 7.3.7: for all `ε ∈ [0, 1/2]`, `H(ε) ≤ O(ε log(1/ε))` and
`1 − H(1/2 + ε) ≤ 2ε²/ln 2 + O(ε⁴)`, where `H` is the binary entropy in bits and `log` is base 2.
The constants of both `O`'s are uniform over `ε ∈ [0, 1/2]`. -/
theorem binEntropy_estimates :
    (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 →
        binEntropy2 ε ≤ C₁ * (ε * Real.logb 2 (1 / ε))) ∧
      ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 →
        1 - binEntropy2 (1 / 2 + ε) ≤ 2 * ε ^ 2 / Real.log 2 + C₂ * ε ^ 4 := by
  sorry

/-- Arunachalam p.162, Fact 7.3.8: for every positive integer `n`, `binom(n, k) ≤ 2^{n H(k/n)}`
for all `k ≤ n`, and `∑_{i=0}^{m} binom(n, i) ≤ 2^{n H(m/n)}` for all `m ≤ n/2` (`H` the binary
entropy in bits). -/
theorem choose_le_two_pow_binEntropy {n : ℕ} (hn : 1 ≤ n) :
    (∀ k : ℕ, k ≤ n →
        ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((k : ℝ) / (n : ℝ)))) ∧
      ∀ m : ℕ, 2 * m ≤ n →
        ∑ i ∈ Finset.range (m + 1), ((n.choose i : ℕ) : ℝ) ≤
          (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((m : ℝ) / (n : ℝ))) := by
  sorry

/-- Arunachalam p.162, Fact 7.3.9 (Helstrom bound): let `b ∈ {0,1}` be uniform and let an
algorithm, given the pure state `|ψ_b⟩`, guess `b`; its guess is the outcome of a two-outcome
POVM `{M_0, M_1}` (ancillas and unitaries absorbed). Then
1. it guesses correctly with probability at most `1/2 + (1/2)√(1 − |⟨ψ_0|ψ_1⟩|²)`;
2. if it guesses correctly with probability `≥ 1 − δ`, then `|⟨ψ_0|ψ_1⟩| ≤ 2√(δ(1 − δ))`.

In part 2 we assume `δ ∈ [0, 1/2]`, which the source leaves implicit: for `δ > 1/2` the
conclusion fails at `ψ_0 = ψ_1` (any blind guess succeeds with probability `1/2 ≥ 1 − δ`). -/
theorem helstrom_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : Bool → EuclideanSpace ℂ ι) (hψ : ∀ b, IsState (ψ b))
    (M : Bool → Matrix ι ι ℂ) (hM : IsPOVM M) :
    ensembleSuccess (fun _ => (1 / 2 : ℝ)) ψ M ≤
        1 / 2 + 1 / 2 * Real.sqrt (1 - ‖inner ℂ (ψ false) (ψ true)‖ ^ 2) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → 1 - δ ≤ ensembleSuccess (fun _ => (1 / 2 : ℝ)) ψ M →
        ‖inner ℂ (ψ false) (ψ true)‖ ≤ 2 * Real.sqrt (δ * (1 - δ)) := by
  sorry

end QAlgorithms.Arunachalam
