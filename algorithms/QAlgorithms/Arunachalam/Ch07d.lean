import QAlgorithms.Defs.LearningHardInstances

/-!
# Arunachalam, Chapter 7 (part d): optimal quantum PAC and agnostic lower bounds by state
identification, noisy PAC learning, codeword states

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N" (PDF pages), §7.5.2–7.6.2: Theorems 7.5.6, 7.5.8, 7.6.1, 7.6.2 and
Lemmas 7.5.7, 7.5.9.

Learners follow the frozen definitions of `QAlgorithms.Defs.Learning`: a quantum learner using
`T` examples is a POVM on `T` copies of the example state, one outcome per hypothesis, fixed before
the target concept and the distribution. The pretty good measurement success probability
`P^PGM(E)` of an ensemble is the frozen `pgmSuccess`. In the lemmas the shattered points `s_i`
enter only as orthonormal labels: `|s_i, b⟩` is the basis vector of `(i, b)`.
-/

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.175–177, Theorem 7.5.6: let `C` be a concept class with `VC-dim(C) = d + 1`, for
sufficiently large `d`. Then for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/20)`, every `(ε, δ)`-PAC
quantum learner for `C` has sample complexity `Ω(d/ε + (1/ε) log(1/δ))`.

The constant `C₀` of the `Ω` and the threshold `d₀` of "sufficiently large `d`" are absolute:
they come before `n`, `C`, `d`, `δ`, `ε` and the learner. -/
theorem quantumPAC_sample_lower_bound_optimal :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d₀ : ℕ,
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 → d₀ ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 20 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQPACLearner C ε δ T M →
              C₀ * ((d : ℝ) / ε + Real.log (1 / δ) / ε) ≤ (T : ℝ) := by
  sorry

/-- Arunachalam p.176–177, Lemma 7.5.7, in the setting of the proof of Theorem 7.5.6:
`ε ∈ (0, 1/20)`; `D(s₀) = 1 − 20ε`, `D(s_i) = 20ε/d` for `i ∈ [d]`; `M ∈ F₂^{d×k}` is the rank-`k`
generator matrix of a `[d, k, r]₂` code with `k ≥ d/4` and distance `r ≥ d/8`; `c^x(s₀) = 0`,
`c^x(s_i) = (Mx)_i`; `1 ≤ T ≤ d/(20e³ε)` and `d ≥ 10` (the hypotheses of Theorem 7.5.1 with
`m = d`, `β = 20ε`). For every `x ∈ {0,1}^k` let `|ψ_x⟩ = ∑_{i ∈ {0,…,d}} √D(s_i) |s_i, c^x(s_i)⟩`
and `E = {(2^{−k}, |ψ_x⟩^{⊗T}) : x ∈ {0,1}^k}`. Then
`P^PGM(E) ≤ (4e / 2^{d/4 + Tε}) e^{8800T²ε²/d + 4√(5Tdε)}`. -/
theorem pgm_pac_hard_ensemble {d k T : ℕ} {ε : ℝ} (hd : 10 ≤ d) (hε : 0 < ε) (hε' : ε < 1 / 20)
    (M : Matrix (Fin d) (Fin k) (ZMod 2)) (hM : M.rank = k) (hkd : k ≤ d) (hdk : d ≤ 4 * k)
    (hdist : ∀ x y : Fin k → ZMod 2, x ≠ y →
      (d : ℝ) / 8 ≤ (hammingDist (M.mulVec x) (M.mulVec y) : ℝ))
    (hT : 1 ≤ T) (hTd : (T : ℝ) ≤ (d : ℝ) / (20 * Real.exp 3 * ε)) :
    pgmSuccess (fun _ : Fin k → ZMod 2 => ((2 : ℝ) ^ k)⁻¹)
        (fun x => tensorPow T (exampleState (pacHardConcept M x) (pacHardDist d ε))) ≤
      4 * Real.exp 1 / (2 : ℝ) ^ ((d : ℝ) / 4 + (T : ℝ) * ε) *
        Real.exp (8800 * (T : ℝ) ^ 2 * ε ^ 2 / (d : ℝ) +
          4 * Real.sqrt (5 * (T : ℝ) * (d : ℝ) * ε)) := by
  sorry

/-- Arunachalam p.178–180, Theorem 7.5.8: let `C` be a concept class with `VC-dim(C) = d`, for
sufficiently large `d`. Then for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/10)`, every `(ε, δ)`-agnostic
quantum learner for `C` has sample complexity `Ω(d/ε² + (1/ε²) log(1/δ))`.

The constant `C₀` and the threshold `d₀` are absolute (before every other object). The proof's
parameter choice is inconsistent (the text picks `α = 20ε`, Lemma 7.5.9 computes with `α = 10ε`);
the theorem is stated as written. -/
theorem quantumAgnostic_sample_lower_bound_optimal :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d₀ : ℕ,
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d → d₀ ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 10 →
          ∀ (T : ℕ) (M : {c // c ∈ C} →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQAgnosticLearner C ε δ T M →
              C₀ * ((d : ℝ) / ε ^ 2 + Real.log (1 / δ) / ε ^ 2) ≤ (T : ℝ) := by
  sorry

/-- Arunachalam p.178–180, Lemma 7.5.9, in the setting of the proof of Theorem 7.5.8:
`ε ∈ (0, 1/10)`; `M ∈ F₂^{d×k}` is the rank-`k` generator matrix of a `[d, k, r]₂` code with
`k ≥ d/4` and `r ≥ d/8`; `D_x(s_i, b) = (1/d)(1/2 + (−1)^{(Mx)_i + b} α/2)` on `[d] × {0,1}` with
`α = 10ε` (the value the lemma's proof computes with; recorded discrepancy with the text's
`α = 20ε`); `1 ≤ T ≤ d/(100e³ε²)` and `d ≥ 10` (Theorem 7.5.1 with `m = d`,
`β = 1 − √(1 − 100ε²)`). For `x ∈ {0,1}^k` let
`|ψ_x⟩ = ∑_{(i,b) ∈ [d]×{0,1}} √D_x(s_i, b) |s_i, b⟩` and `E = {(2^{−k}, |ψ_x⟩^{⊗T})}`. Then
`P^PGM(E) ≤ (4e / e^{(d ln 2)/4 + 25Tε²}) e^{220000T²ε⁴/d + 20√(Tdε²)}`. -/
theorem pgm_agnostic_hard_ensemble {d k T : ℕ} {ε : ℝ} (hd : 10 ≤ d) (hε : 0 < ε)
    (hε' : ε < 1 / 10) (M : Matrix (Fin d) (Fin k) (ZMod 2)) (hM : M.rank = k) (hkd : k ≤ d)
    (hdk : d ≤ 4 * k)
    (hdist : ∀ x y : Fin k → ZMod 2, x ≠ y →
      (d : ℝ) / 8 ≤ (hammingDist (M.mulVec x) (M.mulVec y) : ℝ))
    (hT : 1 ≤ T) (hTd : (T : ℝ) ≤ (d : ℝ) / (100 * Real.exp 3 * ε ^ 2)) :
    pgmSuccess (fun _ : Fin k → ZMod 2 => ((2 : ℝ) ^ k)⁻¹)
        (fun x => tensorPow T (agnosticExampleState (agnHardDist M ε x))) ≤
      4 * Real.exp 1 / Real.exp ((d : ℝ) * Real.log 2 / 4 + 25 * (T : ℝ) * ε ^ 2) *
        Real.exp (220000 * (T : ℝ) ^ 2 * ε ^ 4 / (d : ℝ) +
          20 * Real.sqrt ((T : ℝ) * (d : ℝ) * ε ^ 2)) := by
  sorry

/-- Arunachalam p.180–181, Theorem 7.6.1: let `C` be a concept class with `VC-dim(C) = d + 1`, for
sufficiently large `d`. Then for every `δ ∈ (0, 1/2)`, `ε ∈ (0, 1/20)` and `η ∈ (0, 1/2)`, every
`(ε, δ)`-PAC quantum learner for `C` with random classification noise rate `η` (given copies of
`∑_x √((1−η)D(x)) |x, c(x)⟩ + √(ηD(x)) |x, 1 − c(x)⟩`, outputting `h` with `err_D(c, h) ≤ ε` with
probability `≥ 1 − δ`, for every `c ∈ C` and every `D`) has sample complexity
`Ω(d/((1−2η)²ε) + log(1/δ)/((1−2η)²ε))`.

The constant `C₀` and the threshold `d₀` are absolute: uniform also in `η`. -/
theorem noisyQuantumPAC_sample_lower_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d₀ : ℕ,
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 → d₀ ≤ d →
        ∀ δ ε η : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 20 → 0 < η → η < 1 / 2 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsNoisyQPACLearner η C ε δ T M →
              C₀ * ((d : ℝ) / ((1 - 2 * η) ^ 2 * ε) +
                Real.log (1 / δ) / ((1 - 2 * η) ^ 2 * ε)) ≤ (T : ℝ) := by
  sorry

/-- Arunachalam p.182, Theorem 7.6.2: let `E = {|ψ_x⟩ = (1/√n) ∑_{i ∈ [n]} |i, (Mx)_i⟩ :
x ∈ {0,1}^k}`, where `M ∈ F₂^{n×k}` is the (rank-`k`) generator matrix of an `[n, k, d]₂` linear
code with `k = Ω(n)`. Then `Ω(k)` copies of an unknown state from `E` (drawn uniformly at random)
are necessary to identify that state with probability at least `4/5`.

`k = Ω(n)` is read as a fixed rate: `k ≥ c₁ n`; the constant `c₀` of `Ω(k)` depends only on `c₁`.
Identifying the state is outputting `x` (rank `k` makes `x ↦ Mx` injective); the measurement is
any POVM on the `T` copies, and success is averaged over the uniform prior. The code distance
plays no role in the statement and is not a binder. -/
theorem codewordState_identification_lower_bound :
    ∀ c₁ : ℝ, 0 < c₁ → ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n k : ℕ) (M : Matrix (Fin n) (Fin k) (ZMod 2)), M.rank = k → c₁ * (n : ℝ) ≤ (k : ℝ) →
        ∀ (T : ℕ) (N : (Fin k → ZMod 2) →
            Matrix (Fin T → Fin n × Bool) (Fin T → Fin n × Bool) ℂ),
          IsPOVM N →
          ensembleSuccess (fun _ : Fin k → ZMod 2 => ((2 : ℝ) ^ k)⁻¹)
              (fun x => tensorPow T (exampleState (codeConcept M x) (uniformDist (Fin n)))) N ≥
            4 / 5 →
          c₀ * (k : ℝ) ≤ (T : ℝ) := by
  sorry

end QAlgorithms.Arunachalam
