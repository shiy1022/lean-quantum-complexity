import QAlgorithms.Defs.LearningHardInstances

/-!
# Arunachalam, Chapter 7 (part c): quantum sample complexity lower bounds and the technical
theorem of §7.5.1

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N" (PDF pages): the information-theoretic quantum PAC and agnostic lower bounds
(Theorems 7.4.6, 7.4.7) and the claims and lemma in the proof of Theorem 7.5.1 (Claims 7.5.2,
7.5.3, 7.5.5, Lemma 7.5.4). Logarithms are base 2.
-/

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.168–169, Theorem 7.4.6: let `C` be a concept class with `VC-dim(C) = d + 1`.
Then for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/4)`, every `(ε, δ)`-PAC quantum learner for `C` has
sample complexity `Ω(d/(ε log(d/ε)) + log(1/δ)/ε)`.

Recorded corrections (trap 30), as for Theorem 7.4.3: the constant of the `Ω` may depend on an
upper bound `δ₀ < 1/2` on `δ` (the `log(1/δ)/ε` part is Lemma 7.4.1, which cannot hold uniformly
as `δ → 1/2`), and `C` is non-trivial (the hypothesis of Lemma 7.4.1; binding only at `d = 0`). The
constant is uniform over `n`, `C`, `d`, `δ ∈ (0, δ₀]` and `ε`. -/
theorem quantumPAC_sample_lower_bound_info (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ < 1 / 2) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d + 1 →
        IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQPACLearner C ε δ T M →
              C₀ * ((d : ℝ) / (ε * Real.logb 2 ((d : ℝ) / ε)) + Real.logb 2 (1 / δ) / ε) ≤
                (T : ℝ) := by
  sorry

/-- Arunachalam p.169–170, Theorem 7.4.7: let `C` be a concept class with `VC-dim(C) = d`. Then
for every `δ ∈ (0, 1/2)` and `ε ∈ (0, 1/4)`, every `(ε, δ)`-agnostic quantum learner for `C` has
sample complexity `Ω(d/(ε² log(d/ε)) + log(1/δ)/ε²)`.

Recorded corrections (trap 30), as for Theorem 7.4.4: the constant may depend on an upper bound
`δ₀ < 1/2` on `δ`, and `d ≥ 1` (at `d = 0` the class has a single concept, which is output with no
samples). The constant is uniform over `n`, `C`, `d`, `δ ∈ (0, δ₀]` and `ε`. -/
theorem quantumAgnostic_sample_lower_bound_info (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ < 1 / 2) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)) (d : ℕ), vcDimClass C = d → 1 ≤ d →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : {c // c ∈ C} →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQAgnosticLearner C ε δ T M →
              C₀ * ((d : ℝ) / (ε ^ 2 * Real.logb 2 ((d : ℝ) / ε)) +
                  Real.logb 2 (1 / δ) / ε ^ 2) ≤ (T : ℝ) := by
  sorry

/-- Arunachalam p.171, Claim 7.5.2: for `g : {0,1}^k → ℝ` and `P ∈ ℝ^{2^k × 2^k}` defined by
`P(x, y) = g(x + y)` (addition over `F₂`), the eigenvalues of `P` are
`{2^k ĝ(Q) : Q ∈ {0,1}^k}`, with `ĝ(Q) = E_z[g(z)(−1)^{Q·z}]`.

Stated with multiplicities, as the proof gives it (`H P H⁻¹ = diag(2^k ĝ(Q))`): the
characteristic polynomial of `P` is `∏_Q (X − 2^k ĝ(Q))`; and, as a set, the spectrum of `P` is
`{2^k ĝ(Q)}`. -/
theorem xorConv_eigenvalues {k : ℕ} (g : (Fin k → ZMod 2) → ℝ) :
    (xorConvMatrix g).charpoly =
        ∏ Q : Fin k → ZMod 2, (Polynomial.X - Polynomial.C ((2 : ℝ) ^ k * boolFourier g Q)) ∧
      spectrum ℝ (xorConvMatrix g) = Set.range fun Q => (2 : ℝ) ^ k * boolFourier g Q := by
  sorry

/-- Arunachalam p.170–172, Claim 7.5.3, in the setting of Theorem 7.5.1: `m ≥ 10`,
`f(z) = (1 − β|z|/m)^T` on `{0,1}^m` with `β ∈ (0, 1]` and `T ∈ [1, m/(e³β)]` (a natural number),
`k ≤ m`, `M ∈ F₂^{m×k}` of rank `k`, and `A(x, y) = (f ∘ M)(x + y)` for `x, y ∈ {0,1}^k`. Then for
all `x ∈ {0,1}^k`,
`√A(x, x) = 2^{−k/2} ∑_{Q ∈ {0,1}^k} √(∑_{S ∈ {0,1}^m : Mᵀ S = Q} f̂(S))`,
where `√A` is the positive semidefinite square root of `A`. -/
theorem sqrtA_diag {m k T : ℕ} {β : ℝ} (hm : 10 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1) (hT : 1 ≤ T)
    (hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (hk : k ≤ m)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (hM : M.rank = k) (x : Fin k → ZMod 2) :
    psdSqrt (xorConvMatrix fun z => weightPowFun m β T (M.mulVec z)) x x =
      (Real.sqrt ((2 : ℝ) ^ k))⁻¹ *
        ∑ Q : Fin k → ZMod 2, Real.sqrt
          (∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
            boolFourier (weightPowFun m β T) S) := by
  sorry

/-- Arunachalam p.172–175, Lemma 7.5.4, in the setting of Theorem 7.5.1 (`m ≥ 10`,
`T ∈ [1, m/(e³β)]` a natural number, which the proof uses): for `β ∈ (0, 1]`, the Fourier
coefficients of `f(z) = (1 − β|z|/m)^T` on `{0,1}^m` satisfy
`0 ≤ f̂(S) ≤ 4e (1 − β/2)^T (Tβ/m)^q e^{22T²β²/m}` for all `S` with `|S| = q`. -/
theorem fourier_weightPow_bound {m T : ℕ} {β : ℝ} (hm : 10 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (S : Fin m → ZMod 2) :
    0 ≤ boolFourier (weightPowFun m β T) S ∧
      boolFourier (weightPowFun m β T) S ≤
        4 * Real.exp 1 * (1 - β / 2) ^ T * ((T : ℝ) * β / (m : ℝ)) ^ hammingNorm S *
          Real.exp (22 * (T : ℝ) ^ 2 * β ^ 2 / (m : ℝ)) := by
  sorry

/-- Arunachalam p.173, Claim 7.5.5: fix `S ∈ {0,1}^m` of Hamming weight `|S| = q`. For every
`ℓ ∈ {q, …, T}`, the number of index sequences `(i₁, …, i_ℓ) ∈ [m]^ℓ` with
`e_{i₁} + ⋯ + e_{i_ℓ} = S` (over `F₂`, `e_i` the `i`-th standard basis vector) is at most
`ℓ! · m^{(ℓ−q)/2} / (2^{(ℓ−q)/2} ((ℓ − q)/2)!)` if `ℓ − q` is even, and is `0` otherwise. -/
theorem count_basis_sums {m T ℓ : ℕ} (S : Fin m → ZMod 2) (hqℓ : hammingNorm S ≤ ℓ)
    (hℓT : ℓ ≤ T) :
    (Even (ℓ - hammingNorm S) →
        (((Finset.univ.filter fun i : Fin ℓ → Fin m =>
            ∑ j, Pi.single (i j) (1 : ZMod 2) = S).card : ℕ) : ℝ) ≤
          ((ℓ.factorial : ℕ) : ℝ) * (m : ℝ) ^ ((ℓ - hammingNorm S) / 2) /
            ((2 : ℝ) ^ ((ℓ - hammingNorm S) / 2) *
              (((ℓ - hammingNorm S) / 2).factorial : ℕ))) ∧
      (¬ Even (ℓ - hammingNorm S) →
        (Finset.univ.filter fun i : Fin ℓ → Fin m =>
            ∑ j, Pi.single (i j) (1 : ZMod 2) = S).card = 0) := by
  sorry

end QAlgorithms.Arunachalam
