import QAlgorithms.Defs.IQAE

/-!
# Grinko, Gacon, Zoufal, Woerner, *Iterative quantum amplitude estimation*
(arXiv:1912.05559v3)

Cited "IQAE p.N" (PDF pages). The problem (eq. (1), p.2) is an operator `A` on `n + 1` qubits
with `A|0⟩_n|0⟩ = √(1 − a)|ψ₀⟩_n|0⟩ + √a|ψ₁⟩_n|1⟩`, the last qubit (`Fin.last n`) the flag
qubit; `Q = A S₀ A† S_{ψ₀}` (p.2) is the frozen `iqaeGrover`, and a shot of power `k` measures the
flag qubit of `Q^k A|0⟩` (frozen `iqaeShotProb`). Algorithm 1 (p.3) with `ci = "Clopper-Pearson"`
and FindNextK (Alg. 2, p.4, `r = 2`) is the frozen Markov chain `iqaeStep`/`iqaeRun`; its state
records the confidence interval `[θ_l, θ_u]`, the sequence of powers `k_i` of all iterations
(`kHist`) and the number `N_oracle = Σ_i N_i k_i` of applications of `Q` (B13, p.9).
-/

namespace QAlgorithms.Papers.IQAE21

open QAlgorithms

/-- IQAE Theorem 2 (Appendix C, p.11; Algorithm 1, p.3; Algorithm 2, p.4; eq. (11), p.4;
Clopper–Pearson bounds (C5)–(C7), p.12): let `A` be a unitary on `n + 1` qubits with
`A|0⟩ = √(1 − a)|ψ₀⟩|0⟩ + √a|ψ₁⟩|1⟩` (eq. (1)), `a ∈ [0, 1]`, `|ψ₀⟩, |ψ₁⟩` unit vectors, and
`θ_a = arcsin √a` (`a = sin² θ_a`, eq. (4)). Take `α = 1/20` (confidence `0.95`),
`2^{−200} ≤ ε < π/8`, and `N_shots ∈ {1, …, N_max(ε, α)}`,
`N_max(ε, α) = 69 log((2/α) log₂(π/(4ε)))`. Then IQAE with Clopper–Pearson intervals:
1. performs at most `T = ⌈log₂(π/(8ε))⌉` rounds (a round is the set of iterations with the same
   `k_i`), each of at most `N_max/N_shots` iterations; hence it has halted after
   `T · ⌊N_max/N_shots⌋ + 1` steps of the chain (the last step only checks the loop condition);
2. on every run, `θ_u − θ_l ≤ 2ε` and `a_u − a_l ≤ 2ε`, where `[a_l, a_u] = [sin² θ_l, sin² θ_u]`;
3. `P[θ_a ∉ [θ_l, θ_u]] ≤ α`; 4. `P[a ∉ [a_l, a_u]] ≤ α`;
5. `P[|a − (a_l + a_u)/2| > ε] ≤ α`;
6. on every run, `N_oracle < (14/ε) log((2/α) log₂(π/(4ε)))` (C3).

Corrections of the page (recorded in the chunk's STATUS.md): the Clopper–Pearson bounds of
(C5)–(C6) and Alg. 1 lines 24–25 are printed with `a^min` and `a^max` swapped; the standard
orientation is used (frozen `clopperPearsonLower`/`Upper`). The hypothesis `ε < π/8` is added:
for `π/8 ≤ ε < π/4` the printed algorithm has `T = 0` rounds while its loop still runs, and its
level `α/(2T)` is undefined. -/
theorem iqae_clopperPearson_correct (n : ℕ) (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits (n + 1)) ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ψ0 ψ1 : EuclideanSpace ℂ (Qubits n)) (hψ0 : ‖ψ0‖ = 1) (hψ1 : ‖ψ1‖ = 1)
    (hAeq : act A (zeroKet (n + 1)) =
      (Real.sqrt (1 - a) : ℂ) • snocQubit ψ0 false + (Real.sqrt a : ℂ) • snocQubit ψ1 true)
    (ε : ℝ) (hε0 : (2 : ℝ) ^ (-200 : ℤ) ≤ ε) (hε1 : ε < Real.pi / 8)
    (Nshots : ℕ) (hN1 : 1 ≤ Nshots) (hN2 : (Nshots : ℝ) ≤ iqaeNmax ε (1 / 20)) :
    let F : ℕ := iqaeT ε * ⌊iqaeNmax ε (1 / 20) / Nshots⌋₊ + 1
    let μ : PMF IQAEState := iqaeRun A ψ0 ε (1 / 20) Nshots F
    (∀ s ∈ μ.support,
      s.halted = true ∧
      s.kHist.dedup.length ≤ iqaeT ε ∧
      (∀ k ∈ s.kHist, (s.kHist.count k : ℝ) ≤ iqaeNmax ε (1 / 20) / Nshots) ∧
      s.thetaU - s.thetaL ≤ 2 * ε ∧
      Real.sin s.thetaU ^ 2 - Real.sin s.thetaL ^ 2 ≤ 2 * ε ∧
      (s.oracle : ℝ) < 14 / ε * Real.log (2 / (1 / 20) * Real.logb 2 (Real.pi / (4 * ε)))) ∧
    μ.toOuterMeasure {s | Real.arcsin (Real.sqrt a) ∉ Set.Icc s.thetaL s.thetaU} ≤
      ENNReal.ofReal (1 / 20) ∧
    μ.toOuterMeasure {s | a ∉ Set.Icc (Real.sin s.thetaL ^ 2) (Real.sin s.thetaU ^ 2)} ≤
      ENNReal.ofReal (1 / 20) ∧
    μ.toOuterMeasure {s | ε < |a - (Real.sin s.thetaL ^ 2 + Real.sin s.thetaU ^ 2) / 2|} ≤
      ENNReal.ofReal (1 / 20) := by
  sorry

end QAlgorithms.Papers.IQAE21
