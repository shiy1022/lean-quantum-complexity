import QAlgorithms.Defs.CircuitResources

/-!
# Gilyén–Su–Low–Wiebe, *Quantum singular value transformation and beyond* (arXiv:1806.01838v1)

Cited "GSLW p.N" (PDF pages). Two results:

* Theorem 56 (p.48): polynomial eigenvalue transformation of arbitrary parity (cited by de Wolf,
  Theorem 1, and by Childs, Theorem 29.2);
* Corollary 62 (p.53; Corollary 63 in the published version): robust block-Hamiltonian
  simulation (cited by Nannicini, Theorem 7.19).

Model (Definition 43, p.41). An `(α, a, ε)`-block-encoding of an `s`-qubit operator `A` is an
`(a + s)`-qubit unitary `U` with `‖A − α(⟨0|^{⊗a} ⊗ I) U (|0⟩^{⊗a} ⊗ I)‖ ≤ ε` (operator norm,
ancilla register first): the frozen `IsQubitBlockEncoding a s U α ε A`. The constructed circuit is
an oracle circuit over the one- and two-qubit gates (`twoQubitGateSet`; the circuit has at least
two wires, so a one-qubit gate is a two-qubit gate tensored with an identity) with a single
oracle `U` on `a + s` wires, acting on the `a + 2` ancillas of the new encoding, the `s` system
qubits and `w` further clean ancillas (p.41: ancillas returned exactly to `|0⟩` are purely
ancillary and not part of the encoding). The circuit is fixed before `U` (trap Q2).
-/

namespace QAlgorithms.Papers.GSLW19

open QAlgorithms

/-- **GSLW Theorem 56** (PDF p.48), polynomial eigenvalue transformation of arbitrary parity.

Suppose `U` is an `(α, a, ε)`-encoding of a Hermitian `s`-qubit matrix `A`. If `δ ≥ 0` and
`P ∈ ℝ[x]` is a degree-`d` polynomial with `|P(x)| ≤ 1/2` on `[−1, 1]`, then there is a circuit
`Ũ` which is a `(1, a + 2, 4d√(ε/α) + δ)`-encoding of `P(A/α)`, made of `d` applications of `U`
and `U†`, a single application of controlled-`U` and `O((a + 1)d)` other one- and two-qubit
gates.

Encoding choices: "degree-`d`" is `natDegree P ≤ d` and the use counts are upper bounds; the
circuit depends only on `s, a, d, P, δ` (never on `α, ε, A, U`); the `O((a+1)d)` bound is
`C · (a + 1) · max d 1` with an absolute `C` (at `d = 0` the literal bound `0` is impossible,
since the final circuit has Hadamards on the two new ancillas); the single controlled query may
be controlled-`U` or controlled-`U†` (the count does not fix the adjoint flag); `α > 0` (the
source's `α ∈ ℝ₊`, needed for `A/α`).

**Correction** (trap 30). Printed: no norm condition on `A` beyond what the encoding forces
(`‖A‖ ≤ α + ε`, p.41). Changed: the hypothesis `‖A‖ ≤ α` (`specNorm A ≤ α`) is added. Why: the
proof (p.49) applies Lemma 22 (p.23), which requires `‖A/α‖ ≤ 1`; without it the printed statement
is false: `s = a = 0`, `α = ε = 1`, `A = [2]`, `U = [1]` (a `(1, 0, 1)`-encoding of `A`),
`P = T₈/2`, `d = 8`, `δ = 0` gives `P(A/α) = T₈(2)/2 ≈ 9408`, while every block of a unitary has
norm `≤ 1` and the claimed error is `32`. **Not stated**: the final sentence, that a description of
the circuit is classically computable in time `O(poly(d, log(1/δ)))`, because `P` has real
coefficients and the source fixes no bit model for them. -/
theorem polyEigenvalueTransform_arbitraryParity :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s a d : ℕ) (P : Polynomial ℝ) (δ : ℝ), 0 ≤ δ → P.natDegree ≤ d →
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 / 2) →
        ∃ (w : ℕ) (c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + s) (a + 2 + s + w)),
          c.plainQueryCount 0 ≤ d ∧ c.controlledQueryCount 0 ≤ 1 ∧
          (c.gateCount : ℝ) ≤ C * ((a : ℝ) + 1) * (max d 1 : ℕ) ∧
          ∀ (α ε : ℝ) (A : Matrix (Qubits s) (Qubits s) ℂ)
            (U : Matrix (Qubits (a + s)) (Qubits (a + s)) ℂ),
            0 < α → 0 ≤ ε → A.IsHermitian → specNorm A ≤ α →
            IsQubitBlockEncoding a s U α ε A →
            ∃ V : Matrix (Qubits (a + 2 + s)) (Qubits (a + 2 + s)) ℂ,
              ImplementsWithCleanAncillas (c.unitary fun _ => U) V ∧
              IsQubitBlockEncoding (a + 2) s V 1 (4 * d * Real.sqrt (ε / α) + δ)
                (Polynomial.aeval ((α : ℂ)⁻¹ • A) P) := by
  sorry

/-- **GSLW Corollary 62** (PDF p.53; Corollary 63 in the published version), robust
block-Hamiltonian simulation.

Let `t ∈ ℝ`, `ε ∈ (0, 1)` and let `U` be an `(α, a, ε/|2t|)`-block-encoding of the Hamiltonian
`H`. Then one can implement a unitary `V` which is a `(1, a + 2, ε)`-block-encoding of `e^{itH}`,
with `6α|t| + 9 log(12/ε)` uses of `U` or its inverse, `3` uses of controlled-`U` or its inverse,
`O(a(α|t| + log(2/ε)))` two-qubit gates and `O(1)` ancilla qubits.

Encoding choices: `log` is the natural logarithm (the proof's `ln(12/ε)`); the circuit depends
on `s, a, t, ε, α` only (not on `H` or `U`); "`O(1)` ancilla qubits" is `w ≤ C` clean ancillas
beyond the `a + 2` encoding ancillas, with an absolute `C`; the gate bound
`O(a(α|t| + log(2/ε)))` is encoded as `C · (a + 1) · (α|t| + log(2/ε))` (at `a = 0` the literal
bound `0` is impossible, the proof via Theorem 56 gives `O((a + 1)d)`); "Hamiltonian" means
Hermitian. At `t = 0` the source's `ε/|2t|` is undefined; Lean's `ε/0 = 0` makes the hypothesis an
exact encoding there. -/
theorem robustBlockHamiltonianSimulation :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s a : ℕ) (t ε α : ℝ), 0 < ε → ε < 1 → 0 < α →
        ∃ (w : ℕ) (c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + s) (a + 2 + s + w)),
          (w : ℝ) ≤ C ∧
          (c.plainQueryCount 0 : ℝ) ≤ 6 * α * |t| + 9 * Real.log (12 / ε) ∧
          c.controlledQueryCount 0 ≤ 3 ∧
          (c.gateCount : ℝ) ≤ C * ((a : ℝ) + 1) * (α * |t| + Real.log (2 / ε)) ∧
          ∀ (H : Matrix (Qubits s) (Qubits s) ℂ) (U : Matrix (Qubits (a + s)) (Qubits (a + s)) ℂ),
            H.IsHermitian → IsQubitBlockEncoding a s U α (ε / |2 * t|) H →
            ∃ V : Matrix (Qubits (a + 2 + s)) (Qubits (a + 2 + s)) ℂ,
              ImplementsWithCleanAncillas (c.unitary fun _ => U) V ∧
              IsQubitBlockEncoding (a + 2) s V 1 ε
                (NormedSpace.exp ((Complex.I * (t : ℂ)) • H)) := by
  sorry

end QAlgorithms.Papers.GSLW19
