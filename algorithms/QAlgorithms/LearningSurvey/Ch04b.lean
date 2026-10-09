import QAlgorithms.Defs.LearningHardInstances

/-!
# Arunachalam–de Wolf survey, §4.2–4.4: sample complexity of quantum PAC and agnostic learning,
and PAC learnability of quantum states

S. Arunachalam, R. de Wolf, *A survey of quantum learning theory* (2017), cited "survey p.N"
(PDF pages).
-/

namespace QAlgorithms.LearningSurvey

open MeasureTheory QAlgorithms.Learning

/-- survey p.13, Theorem 4.12 ([AW17]): optimal quantum PAC sample-complexity lower bound.
Let `C` be a concept class on `{0,1}^n` with VC dimension `d + 1`. For every `δ ∈ (0, 1/2)` and
`ε ∈ (0, 1/20)`, every `(ε, δ)`-quantum PAC learner for `C` (a POVM on `T` copies of the quantum
example, one outcome per hypothesis, correct for every `c ∈ C` and every distribution `D`) uses
`T = Ω(d/ε + (1/ε) log(1/δ))` copies.

Corrected statement (trap 30): the `Ω` carries a threshold `d₀` on `d` (the source's proof needs
"`d` a sufficiently large constant", p.13; this is also the run's asymptotic convention). Without
it the printed statement is false: for `C = {c₁, c₂}` differing at one point (VC dimension 1,
`d = 0`), one copy measured in the computational basis, with a fair coin when the distinguishing
point is not seen, is an `(ε, 1/2 − ε/2)`-learner, while `K log(1/δ)/ε → ∞` as `ε → 0`. -/
theorem quantumPAC_sampleLowerBound :
    ∃ K : ℝ, 0 < K ∧ ∃ d₀ : ℕ, ∀ (n d : ℕ) (C : Finset (Qubits n → Bool)), d₀ ≤ d →
      vcDimClass C = d + 1 →
      ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 20 →
      ∀ (T : ℕ) (M : (Qubits n → Bool) →
          Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
        IsQPACLearner C ε δ T M →
        K * ((d : ℝ) / ε + (1 / ε) * Real.log (1 / δ)) ≤ (T : ℝ) := by sorry

/-- Corrected statement. survey p.13, Theorem 4.13 ([AW17, Theorem 17]). Printed: for `m ≥ 10`,
`f(w) = (1 − β|w|/m)^T` with `β ∈ (0, 1]`, `T ∈ [1, m/(e³β)]`, `k ≤ m`, `M ∈ F₂^{m×k}` of rank `k`
and `A(z, y) = (f ∘ M)(z ⊕ y)`, one has `√A(z, z) ≤ e^{O(Tβ²/m + √(Tmβ))}` for all `z`.

Changed: the bound carries the factor `2^{−k/2}`, i.e.
`√A(z, z) ≤ 2^{−k/2} · e^{K(Tβ²/m + √(Tmβ))}` with an absolute `K > 0`.

Why: as printed the bound is contentless. For integer `T`, `f ∘ M` has nonnegative Fourier
coefficients, so `A` is positive semidefinite with `A(z, z) = f(0) = 1`, and `√A(z, z) ≤ 1` always.
The source's own use (p.14, p.15: `P_pgm = Σ_z √G(z,z)² ≤ e^{O(Tε²/d + √(Tdε)) − d − Tε}`, with
`G = A/2^k`, so `P_pgm = √A(z,z)²`) needs a decaying factor that the printed statement drops
(trap 30). The decay that holds for every `k ≤ m` is `2^{−k/2}`. It cannot be `k`-independent
(at `k = 0`, `√A = 1`), and its rate is tight (at `T = 1`, `β → 0`, `√A(z,z) → 2^{−k/2}`). With
the proof's `k ≥ d/4` it gives the source's `e^{−Ω(d)}`.

`T` is a natural number (the number of copies in both applications), so `√A` is the positive
semidefinite square root (`psdSqrt`); `√A(z, z)` is the `(z, z)` entry of that root. -/
theorem sqrtGram_diag_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (m k : ℕ) (β : ℝ) (T : ℕ) (M : Matrix (Fin m) (Fin k) (ZMod 2))
      (z : Fin k → ZMod 2), 10 ≤ m → k ≤ m → 0 < β → β ≤ 1 → 1 ≤ T →
      (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β) → M.rank = k →
      psdSqrt (xorConvMatrix fun x => weightPowFun m β T (M.mulVec x)) z z ≤
        (Real.sqrt 2)⁻¹ ^ k *
          Real.exp (K * ((T : ℝ) * β ^ 2 / (m : ℝ) + Real.sqrt ((T : ℝ) * (m : ℝ) * β))) := by sorry

/-- survey p.14, Theorem 4.15 ([AW17]): optimal quantum agnostic sample-complexity lower bound.
Let `C` be a concept class on `{0,1}^n` with VC dimension `d`. For every `δ ∈ (0, 1/2)` and
`ε ∈ (0, 1/10)`, every `(ε, δ)`-quantum agnostic learner for `C` (a POVM on `T` copies of
`Σ_{(x,b)} √D(x,b) |x, b⟩` whose outcomes are concepts of `C`, outputting with probability
`≥ 1 − δ` an `h ∈ C` with `err_D(h) ≤ opt_D(C) + ε`, for every distribution `D`) uses
`T = Ω(d/ε² + (1/ε²) log(1/δ))` copies.

Corrected statement (trap 30): the `Ω` carries a threshold `d₀` on `d` (the source's proof needs
the linear code of p.14, which exists for `d` a sufficiently large constant). Without it the
printed statement is false: at `d = 0` the class has at most one concept and `T = 0` suffices; at
`d = 1`, for `C = {c, ¬c}`, one copy measured in the computational basis (output `c` iff the label
agrees with `c`) is an `(ε, 1/2 − ε/2)`-learner, while `K/ε² → ∞` as `ε → 0`. -/
theorem quantumAgnostic_sampleLowerBound :
    ∃ K : ℝ, 0 < K ∧ ∃ d₀ : ℕ, ∀ (n d : ℕ) (C : Finset (Qubits n → Bool)), d₀ ≤ d →
      vcDimClass C = d →
      ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 10 →
      ∀ (T : ℕ) (M : {c // c ∈ C} →
          Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
        IsQAgnosticLearner C ε δ T M →
        K * ((d : ℝ) / ε ^ 2 + (1 / ε ^ 2) * Real.log (1 / δ)) ≤ (T : ℝ) := by sorry

open Classical in
/-- survey p.15, Theorem 4.16 ([Aar07]): PAC learnability of quantum states. There is a
polynomial `p` such that for every number of qubits `n` and all `δ, ε, γ > 0` there is a learner
using `T ≤ n · p(1/ε, 1/γ, log(1/δ))` measurement results with the following property: for every
`n`-qubit state `ρ` and every distribution `D` on the two-outcome measurements (effects `E`,
`0 ≤ E ≤ Id`), given `(E₁, b₁), …, (E_T, b_T)` with the `Eᵢ` i.i.d. from `D` and, independently
given the `Eᵢ`, `Pr[bᵢ = 1] = Tr(Eᵢ ρ)`, with probability `≥ 1 − δ` the learner outputs (the
classical description of) a state `σ` with `Pr_{E∼D}[|Tr(Eσ) − Tr(Eρ)| > γ] ≤ ε`.

The learner is a measurable deterministic map from the `T` results to density matrices; it is
chosen before `ρ` and `D`. `δ < 1` is added (for `δ ≥ 1` the claim is empty, and `log(1/δ) ≤ 0`
would make the bound on `T` meaningless). The joint law of the results is written out: the
`Eᵢ` from the product measure `D^T`, then the bits with probability `∏ᵢ Pr[bᵢ | Eᵢ]`. -/
theorem quantumState_pacLearnable :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ s, 0 ≤ p.coeff s) ∧
      ∀ (n : ℕ) (ε γ δ : ℝ), 0 < ε → 0 < γ → 0 < δ → δ < 1 →
      ∃ T : ℕ, (T : ℝ) ≤ (n : ℝ) * MvPolynomial.eval ![1 / ε, 1 / γ, Real.log (1 / δ)] p ∧
      ∃ L : (Fin T → EffectSet n × Bool) → Matrix (Qubits n) (Qubits n) ℂ,
        Measurable (fun s (i j : Qubits n) => L s i j) ∧ (∀ s, IsDensityMatrix (L s)) ∧
        ∀ ρ : Matrix (Qubits n) (Qubits n) ℂ, IsDensityMatrix ρ →
        ∀ (D : Measure (EffectSet n)) [IsProbabilityMeasure D],
          ∫⁻ Es, ∑ bs : Fin T → Bool,
              ENNReal.ofReal (∏ i, if bs i then effectProb (Es i).1 ρ
                else 1 - effectProb (Es i).1 ρ) *
              (if D {E | γ < |effectProb E.1 (L fun i => (Es i, bs i)) - effectProb E.1 ρ|} ≤
                  ENNReal.ofReal ε then 1 else 0)
            ∂(Measure.pi fun _ : Fin T => D) ≥ ENNReal.ofReal (1 - δ) := by sorry

end QAlgorithms.LearningSurvey
