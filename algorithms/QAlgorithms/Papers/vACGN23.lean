import QAlgorithms.Defs.CircuitResources

/-!
# van Apeldoorn, Cornelissen, Gilyén, Nannicini: pure-state tomography with a state-preparation
unitary

J. van Apeldoorn, A. Cornelissen, A. Gilyén, G. Nannicini, *Quantum tomography using
state-preparation unitaries* (arXiv:2207.08800v1), cited "2207.08800 p.N" (PDF pages):
Proposition 22 (p.22–23), cited by Nannicini as Theorem 5.17.

Conventions. `[d] = {0, …, d − 1}` is `Fin d` (p.6). A `d`-dimensional state is held in
`n = ⌈log₂ d⌉ = Nat.clog 2 d` qubits, index `j` as the most-significant-first expansion of `j`,
indices `≥ d` with amplitude `0` (frozen `padState`). The gate set is the frozen `vacgnGateSet`
(p.6, §2.1): all single-qubit unitaries, CNOT, and the indexed-SWAP gate
`|i⟩|j⟩|x_1⟩⋯|x_D⟩ ↦ |i⟩|j⟩ SWAP_{i,j}(|x_1⟩⋯|x_D⟩)` on a memory of `D` qubits with two
`⌈log₂ D⌉`-qubit index registers (identity on index values `≥ D`, which the paper leaves
unspecified). The input `U` is accessed only through oracle calls (plain, adjoint or controlled)
of an `OracleCircuit` fixed before `U` (trap Q2).
-/

namespace QAlgorithms.Papers.vACGN23

/-- 2207.08800 p.22–23, Proposition 22 (cited by Nannicini as Theorem 5.17). "Let
`|ψ⟩ = Σ_{j∈[d]} α_j |j⟩` be a quantum state, and `U|0⟩ = |ψ⟩`. There is a quantum algorithm that,
with probability at least `1 − δ`, outputs `α̃ ∈ ℝ^d` such that `‖ℜ(α) − α̃‖_∞ ≤ ε`, using
`O((√d/ε) log(d/δ))` applications of `U` and `U†`, `O((√d/ε) log(d/δ) log(d/ε))` indexed-SWAP gates
acting on `d` bits, and `Õ(d + √d/ε)` additional gates. If `ε ≥ 1/√d`, the number of applications
of `U` can be reduced to `Õ(1/ε²)` (while potentially increasing the gate complexity to
`Õ(1/ε⁴)`)."

Formal reading. There are constants `C > 0` and `c` (fixed before `d, ε, δ`) such that for every
`d ≥ 1`, `ε > 0` and `δ ∈ (0, 1)`:

1. there is an oracle circuit over `vacgnGateSet` on `w` qubits started in `|0⟩`, with oracle
   calls to an `n`-qubit unitary, and a classical read-out `out` of the final measurement, such
   that the number of oracle calls (applications of `U` or `U†`, controlled or not) is at most
   `C (√d/ε) log(2 + d/δ)`, every gate is a single-qubit gate, a CNOT or an indexed-SWAP gate on
   a memory of exactly `d` qubits, the number of the latter is at most
   `C (√d/ε) log(2 + d/δ) log(2 + d/ε)` and the number of the former ("additional gates") is at
   most `C (d + √d/ε) L^c`, `L = log(2 + d) + log(2 + 1/ε) + log(2 + 1/δ)`; and for **every** unit
   vector `α ∈ ℂ^d` and every unitary `U` with `U|0⟩ = |ψ⟩`, the measured outcome `z` satisfies
   `|ℜ(α_j) − out(z)_j| ≤ ε` for all `j` with probability at least `1 − δ`;
2. if `ε ≥ 1/√d`, there is such a circuit (with indexed-SWAP gates of any memory size) with at
   most `C (1/ε²) L^c` oracle calls and at most `C (1/ε⁴) L^c` gates in total, with the same
   success guarantee.

The paper's computer may adapt its gates to intermediate measurements (p.6). The algorithm of
clause 1 is non-adaptive; that of clause 2 measures first and then runs clause 1 on the observed
indices. Both are stated in the coherent-circuit model (one circuit, one final measurement,
classical post-processing such as medians and rescaling in `out`); by deferred measurement this
costs only the reversible simulation of the classical control, which the paper's convention
(classical computation counted up to polylog factors) absorbs into the `Õ`. The logarithms
`log(d/δ)`, `log(d/ε)` are taken as `log(2 + ·)` so that the `O`-bounds do not vanish at the
degenerate corner `d = 1`, `δ → 1` (the base of the logarithm is absorbed in `C`). -/
theorem realPart_linf_tomography :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ε δ : ℝ), 0 < ε → 0 < δ → δ < 1 →
      (∃ (w : ℕ) (circ : OracleCircuit vacgnGateSet (fun _ : Fin 1 => Nat.clog 2 d) w)
          (out : Qubits w → Fin d → ℝ),
        (circ.queryCount 0 : ℝ) ≤ C * (Real.sqrt d / ε) * Real.log (2 + d / δ) ∧
          circ.gateCount ≤
            circ.gateCountWhere (fun g => (∃ M : Matrix Bool Bool ℂ,
                M ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 M) ∨ g = Gate.ofMatrix2 cnot) +
              circ.gateCountWhere (fun g => g = indexedSwapGate d) ∧
          (circ.gateCountWhere (fun g => g = indexedSwapGate d) : ℝ) ≤
            C * (Real.sqrt d / ε) * Real.log (2 + d / δ) * Real.log (2 + d / ε) ∧
          (circ.gateCountWhere (fun g => (∃ M : Matrix Bool Bool ℂ,
                M ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 M) ∨
              g = Gate.ofMatrix2 cnot) : ℝ) ≤
            C * (d + Real.sqrt d / ε) *
              (Real.log (2 + d) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          ∀ α : EuclideanSpace ℂ (Fin d), ‖α‖ = 1 →
            ∀ U ∈ Matrix.unitaryGroup (Qubits (Nat.clog 2 d)) ℂ,
              act U (zeroKet (Nat.clog 2 d)) = padState (Nat.clog 2 d) α →
              1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
                fun z => ∀ j : Fin d, |(α j).re - out z j| ≤ ε) ∧
      (1 / Real.sqrt d ≤ ε →
        ∃ (w : ℕ) (circ : OracleCircuit vacgnGateSet (fun _ : Fin 1 => Nat.clog 2 d) w)
          (out : Qubits w → Fin d → ℝ),
          (circ.queryCount 0 : ℝ) ≤ C * (1 / ε ^ 2) *
              (Real.log (2 + d) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
            (circ.gateCount : ℝ) ≤ C * (1 / ε ^ 4) *
              (Real.log (2 + d) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
            ∀ α : EuclideanSpace ℂ (Fin d), ‖α‖ = 1 →
              ∀ U ∈ Matrix.unitaryGroup (Qubits (Nat.clog 2 d)) ℂ,
                act U (zeroKet (Nat.clog 2 d)) = padState (Nat.clog 2 d) α →
                1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
                  fun z => ∀ j : Fin d, |(α j).re - out z j| ≤ ε) := by
  sorry

end QAlgorithms.Papers.vACGN23
