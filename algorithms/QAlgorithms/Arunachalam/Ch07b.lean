import QAlgorithms.Defs.Learning

/-!
# Arunachalam, Chapter 7 (part b): subadditivity and the information-theoretic lower bounds

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N" (PDF pages), §7.3.3–7.4.3: subadditivity of von Neumann entropy (Fact 7.3.10),
the VC-independent quantum lower bounds (Lemmas 7.4.1, 7.4.2) and the classical PAC, agnostic and
average-agnostic lower bounds (Theorems 7.4.3, 7.4.4, 7.4.5).

Learners follow the frozen definitions of `QAlgorithms.Defs.Learning`: a learner using `T`
examples uses exactly `T` (unused examples can be ignored), a quantum learner is a POVM on `T`
copies of the example state, a classical learner a randomized map from the `T` samples to
hypotheses, and the learner is fixed before the target concept and the distribution.
-/

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.162, Fact 7.3.10 (subadditivity of quantum entropy): for every bipartite
density matrix `ρ_AB` on `H_A ⊗ H_B`, `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`, where `S(ρ) = −Tr(ρ log ρ)`
(log base 2, §7.3.1) and `ρ_A = Tr_B ρ_AB`, `ρ_B = Tr_A ρ_AB` are the partial traces. -/
theorem vnEntropy_subadditive {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : IsDensityMatrix ρ) :
    vnEntropy ρ ≤ vnEntropy (traceRight ρ) + vnEntropy (traceLeft ρ) := by
  sorry

/-- Arunachalam p.163, Lemma 7.4.1 ([AS05]): for a non-trivial concept class
`C ⊆ {c : {0,1}^n → {0,1}}` (footnote 5: neither a single concept nor a pair of complementary
concepts), every `(ε, δ)`-PAC quantum learner for `C` with `ε ∈ (0, 1/4)` uses
`Ω((1/ε) log(1/δ))` quantum examples.

Corrected statement (trap 30): with one constant for all `δ ∈ (0, 1/2)` the lemma is false (a
single computational-basis measurement of one example succeeds with probability `1/2 + ε/2` on
`C = {0, 1_{x}}`, so `δ = 1/2 − ε/2` needs `T = 1` while `log(1/δ)/ε → ∞`). The proof's bound
`(1 − p)^T ≤ 2√(δ(1 − δ))` gives `Ω(log(1/δ)/ε)` uniformly for `δ ∈ (0, δ₀]` with `δ₀ < 1/2`;
the constant depends on `δ₀` only, never on `n`, `C`, `ε`, `δ`. -/
theorem qpac_lower_bound_log :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQPACLearner C ε δ T M → C₀ * (Real.log (1 / δ) / ε) ≤ T := by
  sorry

/-- Arunachalam p.163, Lemma 7.4.2: for a non-trivial concept class `C`, every
`(ε, δ)`-agnostic quantum learner for `C` with `ε ∈ (0, 1/4)` (outputting `h ∈ C` with
`err_D(h) ≤ opt_D(C) + ε` with probability `≥ 1 − δ`, for every distribution `D` on
`{0,1}^{n+1}`) uses `Ω((1/ε²) log(1/δ))` quantum examples `∑_{(x,b)} √D(x,b) |x, b⟩`.

Corrected statement (trap 30), as for Lemma 7.4.1: the constant is uniform over
`δ ∈ (0, δ₀]` for each `δ₀ < 1/2` (near `δ = 1/2` two-state discrimination needs only
`O(η²/ε²)` copies to succeed with probability `1/2 + η`). -/
theorem qagnostic_lower_bound_log :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : {c // c ∈ C} →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQAgnosticLearner C ε δ T M → C₀ * (Real.log (1 / δ) / ε ^ 2) ≤ T := by
  sorry

/-- Arunachalam p.163–165, Theorem 7.4.3: for a concept class `C` with `VC-dim(C) = d + 1`,
every (randomized, possibly improper) classical `(ε, δ)`-PAC learner for `C` with
`ε ∈ (0, 1/4)` uses `Ω(d/ε + log(1/δ)/ε)` examples.

Corrected statement (trap 30): the constant is uniform over `δ ∈ (0, δ₀]` for each
`δ₀ < 1/2` (the `log(1/δ)/ε` part is Lemma 7.4.1, see there); and `C` is assumed non-trivial,
as Lemma 7.4.1, which the proof invokes, requires (at `d = 0` the class `{c, ¬c}` has
VC dimension 1 and is learned exactly from one example; for `d ≥ 1` non-triviality is
automatic). -/
theorem pac_lower_bound :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 →
        IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (L : (Fin T → Qubits n × Bool) → PMF (Qubits n → Bool)),
            IsPACLearner C ε δ T L → C₀ * ((d : ℝ) / ε + Real.log (1 / δ) / ε) ≤ T := by
  sorry

/-- Arunachalam p.165–166, Theorem 7.4.4: for a concept class `C` with `VC-dim(C) = d`, every
(randomized) classical `(ε, δ)`-agnostic learner for `C` with `ε ∈ (0, 1/4)` (outputting
`h ∈ C` with `err_D(h) ≤ opt_D(C) + ε` with probability `≥ 1 − δ`, for every distribution `D` on
`{0,1}^{n+1}`) uses `Ω(d/ε² + log(1/δ)/ε²)` samples.

Corrected statement (trap 30): the constant is uniform over `δ ∈ (0, δ₀]` for each
`δ₀ < 1/2` (as Lemma 7.4.2); and `d ≥ 1` is assumed (at `d = 0` the class has at most one
concept, and outputting it without samples is an `(ε, δ)`-agnostic learner). -/
theorem agnostic_lower_bound :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d → 1 ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (L : (Fin T → Qubits n × Bool) → PMF (Qubits n → Bool)),
            IsAgnosticLearner C ε δ T L →
              C₀ * ((d : ℝ) / ε ^ 2 + Real.log (1 / δ) / ε ^ 2) ≤ T := by
  sorry

/-- Arunachalam p.166–168, Theorem 7.4.5: for a concept class `C` with `VC-dim(C) = d` and every
`ε ∈ (0, 1/10]`, every `ε`-average agnostic learner for `C` (using `T` samples from `AEX(D)` and
satisfying `E_{(X,Y)∼D^T}[err_D(h_{XY})] − opt_D(C) ≤ ε` for every distribution `D`) has
`T ≥ (d/ε²) · (1/62 − log(2d + 2)/(4d))`, `log` base 2.

The source's "there exists a distribution for which every learner …" is the proof's random
hard distribution `D_a`; a learner is required to be `ε`-good for every unknown `D`, as the
definition on p.166 says. `d ≥ 1` is assumed because the bound divides by `d` (trap 14). -/
theorem avg_agnostic_lower_bound (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ)
    (hd : vcDimClass C = d) (hd1 : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (T : ℕ)
    (L : (Fin T → Qubits n × Bool) → PMF (Qubits n → Bool))
    (hL : IsAvgAgnosticLearner C ε T L) :
    (d : ℝ) / ε ^ 2 * (1 / 62 - Real.logb 2 (2 * d + 2) / (4 * d)) ≤ T := by
  sorry

end QAlgorithms.Arunachalam
