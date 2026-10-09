import QAlgorithms.Defs.CompressedOracle

/-!
# Childs, Chapter 26: the compressed oracle method

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 26 (PDF pp. 133–137).

The random function is `f : [n] → Σ`, `Σ = {0,1}^m` (`Fin n → Qubits m`); a standard query is
the XOR oracle `|x⟩|z⟩ ↦ |x⟩|z ⊕ f(x)⟩` (§26.1, p. 133). The compressed oracle, the compressed
phase oracle `Φ` (26.29) and the projection `P` onto "the oracle contains a zero" are the
frozen definitions `compressedOracle`, `compressedPhaseOracle` and `containsZeroProj`.
-/

namespace QAlgorithms.Childs

/-- Childs, Lemma 26.1 (PDF p. 134; conclusion as in the proof's (26.15), p. 135).
Let `A` be any `t`-query algorithm with workspace `W` (start state a unit vector, unitaries
fixed independently of the oracle), whose final computational-basis measurement of its own
registers is turned into `k` input–output pairs `(x_1, z_1), …, (x_k, z_k)` by `out`, and let
`R ⊆ [n] × Σ`. Let `p` be the probability, over a uniformly random `f` and the measurement,
that `f(x_i) = z_i` and `(x_i, z_i) ∈ R` for all `i` (`randomOracleSuccess`). Let `p'` be the
probability that, running `A` with the compressed oracle and measuring all registers including
the oracle register, `(x_i, z_i) ∈ R` and the oracle register `x_i` holds `y_{x_i} = z_i` for all
`i` (`compressedSuccess`). Then `√p ≤ √p' + √(k / 2^m)`. -/
theorem compressed_oracle_success_bound {n m k : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {t : ℕ} (A : QueryAlg (Fin n) (Qubits m) W t)
    (out : (Fin n × Qubits m) × W → (Fin k → Fin n × Qubits m))
    (R : Finset (Fin n × Qubits m)) :
    Real.sqrt (randomOracleSuccess A out R) ≤
      Real.sqrt (compressedSuccess A out R) + Real.sqrt ((k : ℝ) / 2 ^ m) := by
  sorry

/-- Childs, Fact 26.2 (PDF p. 136): for every state `|ψ⟩` of the registers
`|x, z, w, y⟩` (input `x ∈ [n]`, output `z ∈ Σ`, workspace `w`, oracle register
`y ∈ (Σ ∪ {⊥})^n`, (26.30)), one application of the compressed phase oracle `Φ` (26.29) raises
the norm of the projection `P` onto basis states whose oracle register contains a zero by at
most `√(2 / 2^m)`: `‖P Φ |ψ⟩‖ ≤ ‖P |ψ⟩‖ + √(2/2^m)`. -/
theorem compressedPhaseOracle_containsZero_le {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (ψ : EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))))
    (hψ : IsState ψ) :
    ‖act (containsZeroProj n m W) (act (compressedPhaseOracle n m W) ψ)‖ ≤
      ‖act (containsZeroProj n m W) ψ‖ + Real.sqrt (2 / 2 ^ m) := by
  sorry

end QAlgorithms.Childs
