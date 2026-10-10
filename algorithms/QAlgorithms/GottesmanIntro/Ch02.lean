import QAlgorithms.Defs.FTCircuit

/-!
# Gottesman, *An introduction to quantum error correction*, §§1–2.2

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages): Theorems 1–4.

A quantum operation is the source's eq. (23) (p.4–5), a superoperator with a finite normalized
Kraus family (`IsChannel`); a quantum code is a subspace of the Hilbert space (p.3); "the code
corrects the errors `S`" is the frozen `Corrects C S` (one recovery operation for all errors of
`S`, restoring every normalized codeword).
-/

namespace QAlgorithms.GottesmanIntro

open scoped Matrix

open QAlgorithms Stabilizer

/-- Gottesman intro p.2, Theorem 1 (No-Cloning): on a Hilbert space of dimension at least 2,
no quantum operation (eq. (23), p.4–5) maps `|ψ⟩⟨ψ|` to `(|ψ⟩ ⊗ |ψ⟩)(⟨ψ| ⊗ ⟨ψ|)` for every
state `|ψ⟩`. -/
theorem noCloning {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι)
    (Φ : Superop ι (ι × ι)) (hΦ : IsChannel Φ) :
    ¬ ∀ ψ : EuclideanSpace ℂ ι, IsState ψ → Φ (pureDensity ψ) = pureDensity (tensorVec ψ ψ) := by
  sorry

/-- Gottesman intro p.4, Theorem 2: for an `n`-qubit quantum code `C`, (1) if `C` corrects the
errors `A` and `B` (with one recovery operation), it corrects every linear combination of `A`
and `B` (all of them with one recovery operation); (2) if `C` corrects all Pauli errors of
weight at most `t`, it corrects all errors acting on at most `t` qubits (arbitrary, not
necessarily unitary, operators; p.5). -/
theorem corrects_linearCombination (n : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))) :
    (∀ A B : Matrix (Qubits n) (Qubits n) ℂ, Corrects C {A, B} →
      Corrects C (Submodule.span ℂ {A, B} : Set (Matrix (Qubits n) (Qubits n) ℂ))) ∧
    ∀ t : ℕ, Corrects C {M | ∃ P : PauliString n, P.weight ≤ t ∧ M = P.toMatrix} →
      Corrects C {E | ActsOnAtMost t E} := by
  sorry

/-- Gottesman intro p.6, Theorem 3 (Knill–Laflamme): for a linear space `𝓔` of errors on a
finite-dimensional Hilbert space `H` and a subspace `C` of `H`, `C` is a quantum
error-correcting code correcting `𝓔` iff there is a function `c(E)`, independent of the state,
with `⟨ψ|E†E|ψ⟩ = c(E)` for all `E ∈ 𝓔` and all normalized `|ψ⟩ ∈ C` (eq. (29)). -/
theorem knillLaflamme {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝓔 : Submodule ℂ (Matrix ι ι ℂ)) (C : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Corrects C (𝓔 : Set (Matrix ι ι ℂ)) ↔
      ∃ c : Matrix ι ι ℂ → ℂ, ∀ E ∈ 𝓔, ∀ ψ ∈ C, ‖ψ‖ = 1 → inner ℂ ψ (act (Eᴴ * E) ψ) = c E := by
  sorry

/-- Gottesman intro p.7–8, Theorem 4. (1) Quantum Gilbert–Varshamov: if
`(∑_{j=0}^{d-1} 3^j C(n,j)) 2^k ≤ 2^n` (eq. (36)) and `d ≥ 1`, an `[[n, k, d]]` code exists.
(2) Quantum Hamming bound: every nondegenerate `[[n, k, d]]` code satisfies
`(∑_{j=0}^{t} 3^j C(n,j)) 2^k ≤ 2^n` (eq. (35)), `t = ⌊(d-1)/2⌋`. (3) Asymptotics (eq. (37)):
for fixed `p ∈ (0, 1/2)` and every `ε > 0`, for all large `n`, every nondegenerate `[[n, k, d]]`
code with `d ≥ 2pn` has `k/n ≤ 1 - p log₂ 3 - H(p) + ε`, and, when `1 - 2p log₂ 3 - H(2p) > 0`,
some nondegenerate `[[n, k, d]]` code with `d ≥ 2pn` has `k/n ≥ 1 - 2p log₂ 3 - H(2p) - ε`. -/
theorem codeBounds :
    (∀ n k d : ℕ, 1 ≤ d →
      (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n →
      ∃ C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)), IsQCode n k d C) ∧
    (∀ (n k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
      IsNondegenerate C ((d - 1) / 2) →
      (∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n) ∧
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∀ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
        IsNondegenerate C ((d - 1) / 2) → 2 * p * n ≤ d →
        (k : ℝ) / n ≤ 1 - p * Real.logb 2 3 - binEntropy2 p + ε) ∧
      (0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) →
        ∃ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C ∧
          IsNondegenerate C ((d - 1) / 2) ∧ 2 * p * n ≤ d ∧
          1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) - ε ≤ (k : ℝ) / n) := by
  sorry

end QAlgorithms.GottesmanIntro
