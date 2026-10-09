import QAlgorithms.Defs.BlockEncoding

/-!
# Nannicini, Chapter 7 (part a): iterative refinement and operations on block-encodings

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Proposition 7.9 (p.158), Proposition 7.14 (p.160), Proposition 7.18 (pp.161–162),
Lemma 7.20 (p.163). Proposition 7.21 (p.164) is not stated (see `HARD.md` of the unit).

Block-encodings are the frozen `IsBlockEncoding` (Defs. 7.10–7.11, auxiliary register first,
spectral norm). An auxiliary register made of several sub-registers is a product type in the
source's register order (Rem. 7.15: `|·⟩_a |·⟩_b |·⟩_q`), its all-zero state the pair of zero
strings.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini Proposition 7.9 (p.158), iterative refinement (Alg. 5, p.158).

For a constant per-iteration precision `δ ∈ (0, 1)` there is a constant `C > 0` such that, for
every system `A x = b` with `‖b‖ = 1` and every target precision `ε ∈ (0, δ)`, whatever vectors
`x̂^(k)` the solver returns (subject to the guarantee
`‖A x̂^(k) − r^(k−1)/‖r^(k−1)‖‖ ≤ δ` at every iteration the loop actually executes), the loop of
Alg. 5 stops after `K ≤ C log(1/ε)` iterations and the returned `x^(K)` has `‖A x^(K) − b‖ ≤ ε`.
Here `x^(k) = iterRefineX A b xhat k` (`x^(0) = 0`,
`x^(k) = x^(k−1) + ‖r^(k−1)‖ x̂^(k)`) and `r^(k) = b − A x^(k)`. -/
theorem iterRefine_iterations (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N)), ‖b‖ = 1 →
        ∀ ε : ℝ, 0 < ε → ε < δ →
          ∀ xhat : ℕ → EuclideanSpace ℂ (Fin N),
            (∀ k : ℕ, (∀ j ≤ k, ε < ‖b - act A (iterRefineX A b xhat j)‖) →
              ‖act A (xhat (k + 1)) - normalizedVec (b - act A (iterRefineX A b xhat k))‖ ≤ δ) →
            ∃ K : ℕ, (K : ℝ) ≤ C * Real.log (1 / ε) ∧
              (∀ k < K, ε < ‖b - act A (iterRefineX A b xhat k)‖) ∧
              ‖act A (iterRefineX A b xhat K) - b‖ ≤ ε := by
  sorry

/-- Nannicini Proposition 7.14 (p.160), product of block-encodings, with the error term
corrected.

If `U_A` is an `(α, a, ξ_A)`-block-encoding of the `q`-qubit operator `A` and `U_B` a
`(β, b, ξ_B)`-block-encoding of `B`, then on the registers `|·⟩_a |·⟩_b |·⟩_q` (Rem. 7.15) the
unitary `(I_b ⊗ U_A)(I_a ⊗ U_B)` is an `(αβ, a + b, αξ_B + βξ_A + ξ_Aξ_B)`-block-encoding of `AB`.
Here `I_b ⊗ U_A` acts as `U_A` on registers `a, q` and as the identity on `b`, and `I_a ⊗ U_B`
acts as `U_B` on registers `b, q` and as the identity on `a`.

**Correction (trap 30).** The source prints the error `αξ_B + βξ_A`, which is false: with
`q = a = b = 0`, `U_A = U_B = 1`, `α = β = 1`, `A = 1 + ξ_A`, `B = 1 + ξ_B` the error of `AB` is
`ξ_A + ξ_B + ξ_Aξ_B`. The source's proof gives `α‖Ã‖ξ_B + ξ_A‖B‖ ≤ αξ_B + ξ_A(β + ξ_B)`.
The subnormalization factors are nonnegative (`0 ≤ α`, `0 ≤ β`), as the source's "scaled-down"
reading of Def. 7.10 assumes. -/
theorem blockEncoding_mul {q a b : ℕ}
    (UA : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ)
    (UB : Matrix (Qubits b × Qubits q) (Qubits b × Qubits q) ℂ)
    (A B : Matrix (Qubits q) (Qubits q) ℂ) (α β ξA ξB : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : IsBlockEncoding (fun _ => false) UA α ξA A)
    (hB : IsBlockEncoding (fun _ => false) UB β ξB B) :
    IsBlockEncoding ((fun _ => false, fun _ => false) : Qubits a × Qubits b)
      ((Matrix.of fun y z : (Qubits a × Qubits b) × Qubits q =>
          if y.1.2 = z.1.2 then UA (y.1.1, y.2) (z.1.1, z.2) else 0) *
        (Matrix.of fun y z : (Qubits a × Qubits b) × Qubits q =>
          if y.1.1 = z.1.1 then UB (y.1.2, y.2) (z.1.2, z.2) else 0))
      (α * β) (α * ξB + β * ξA + ξA * ξB) (A * B) := by
  sorry

/-- Nannicini Proposition 7.18 (pp.161–162), linear combination of block-encodings, with the
error term corrected for `α < 1`.

Let `A = ∑_{j=0}^{m−1} y_j A^(j)` be a `q`-qubit operator, `(P_L, P_R)` a
`(β, p, ξ₁)`-state-preparation pair for `y` (Def. 7.16), and `U^(j)` an
`(α, a, ξ₂)`-block-encoding of `A^(j)` for each `j < m`. Let
`V = ∑_{j ≤ m−1} |j⟩⟨j| ⊗ U^(j) + (I_p − ∑_{j ≤ m−1} |j⟩⟨j|) ⊗ I_a ⊗ I_q` on the registers
`|·⟩_p |·⟩_a |·⟩_q` (the index `j` of a `p`-bit string is `bitsToNat`, most significant bit
first). Then `(P_L† ⊗ I_{a+q}) V (P_R ⊗ I_{a+q})` (the circuit of the proof, p.162, using `V`,
`P_R` and `P_L†` once each) is an `(αβ, a + p, αξ₁ + max(α, 1)·βξ₂)`-block-encoding of `A`,
with auxiliary register `|·⟩_p |·⟩_a`.

**Correction (trap 30).** The source prints the error `αξ₁ + αβξ₂`; for `α ≥ 1` the stated
error is exactly that. For `α < 1` the printed bound is false: with `m = 1`, `p = a = 0`,
`P_L = P_R = 1`, `y_0 = β`, `U^(0) = 1` and `A^(0) = α·1 + E`, `‖E‖ = ξ₂`, the error is
`βξ₂ > αβξ₂`. The source's proof gives `αξ₁ + ‖y‖₁ξ₂ ≤ αξ₁ + βξ₂`. The subnormalization `α`
and the error `ξ₂` are nonnegative (with `m = 0` nothing else forces `0 ≤ ξ₂`). -/
theorem blockEncoding_linearCombination {q a p m : ℕ}
    (Aj : Fin m → Matrix (Qubits q) (Qubits q) ℂ) (y : Fin m → ℂ) (β ξ₁ : ℝ)
    (PL PR : Matrix (Qubits p) (Qubits p) ℂ) (hP : IsStatePrepPair β ξ₁ y PL PR)
    (U : Fin m → Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ) (α ξ₂ : ℝ)
    (hα : 0 ≤ α) (hξ₂ : 0 ≤ ξ₂)
    (hU : ∀ j, IsBlockEncoding (fun _ => false) (U j) α ξ₂ (Aj j)) :
    IsBlockEncoding ((fun _ => false, fun _ => false) : Qubits p × Qubits a)
      (Matrix.kronecker (Matrix.kronecker (star PL) (1 : Matrix (Qubits a) (Qubits a) ℂ))
          (1 : Matrix (Qubits q) (Qubits q) ℂ) *
        (Matrix.of fun u v : (Qubits p × Qubits a) × Qubits q =>
          if u.1.1 = v.1.1 then
            (if h : bitsToNat u.1.1 < m then U ⟨bitsToNat u.1.1, h⟩ (u.1.2, u.2) (v.1.2, v.2)
              else (1 : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ) (u.1.2, u.2)
                (v.1.2, v.2))
          else 0) *
        Matrix.kronecker (Matrix.kronecker PR (1 : Matrix (Qubits a) (Qubits a) ℂ))
          (1 : Matrix (Qubits q) (Qubits q) ℂ))
      (α * β) (α * ξ₁ + max α 1 * β * ξ₂) (∑ j, y j • Aj j) := by
  sorry

/-- Nannicini Lemma 7.20 (p.163), block-encoding of the diagonal matrix of inner products.

Let `U^(j), V^(j)` (`j ∈ {0,1}^p`) be `(a + 1)`-qubit unitaries with
`U^(j)|0⟩|0⟩_a = |0⟩|ψ_j⟩ + |1⟩|ψ̃_j⟩` and `V^(j)|0⟩|0⟩_a = |0⟩|ϕ_j⟩ + |1⟩|ϕ̃_j⟩`, and let
`U = ∑_j U^(j) ⊗ |j⟩⟨j|`, `V = ∑_j V^(j) ⊗ |j⟩⟨j|` (controlled by the last, `p`-qubit
register). On the registers (first qubit, flag qubit of `U^(j)`, `a` qubits, `p` qubits), the
unitary `(I ⊗ V†)(SWAP ⊗ I_{a+p})(I ⊗ U)` is an `(a + 2)`-block-encoding (subnormalization 1,
error 0) of `diag(⟨ϕ_j|ψ_j⟩)_{j = 0, …, 2^p − 1}`, the auxiliary register being the first
`a + 2` qubits. `I` acts on the first qubit and `SWAP` on the first two. -/
theorem blockEncoding_innerProductDiag {a p : ℕ}
    (U V : Qubits p → Matrix (Bool × Qubits a) (Bool × Qubits a) ℂ)
    (ψ ψt ϕ ϕt : Qubits p → EuclideanSpace ℂ (Qubits a))
    (hUu : ∀ j, U j ∈ Matrix.unitaryGroup (Bool × Qubits a) ℂ)
    (hVu : ∀ j, V j ∈ Matrix.unitaryGroup (Bool × Qubits a) ℂ)
    (hU : ∀ j, act (U j) (ket (false, fun _ => false)) =
      tensorVec (ket false) (ψ j) + tensorVec (ket true) (ψt j))
    (hV : ∀ j, act (V j) (ket (false, fun _ => false)) =
      tensorVec (ket false) (ϕ j) + tensorVec (ket true) (ϕt j)) :
    IsBlockEncoding ((false, (false, fun _ => false)) : Bool × (Bool × Qubits a))
      ((Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.1 ∧ u.2 = v.2 then star (V u.2) u.1.2 v.1.2 else 0) *
        (Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.2.1 ∧ u.1.2.1 = v.1.1 ∧ u.1.2.2 = v.1.2.2 ∧ u.2 = v.2 then 1 else 0) *
        (Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.1 ∧ u.2 = v.2 then U u.2 u.1.2 v.1.2 else 0))
      1 0 (Matrix.diagonal fun j => inner ℂ (ϕ j) (ψ j)) := by
  sorry

end QAlgorithms.Nannicini
