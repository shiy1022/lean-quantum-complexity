import QAlgorithms.Defs.QuantumInformation

/-!
# Cleve, van Dam, Nielsen, Tapp, *Quantum entanglement and the communication complexity of the
inner product function*

R. Cleve, W. van Dam, M. Nielsen, A. Tapp, arXiv:quant-ph/9708019v3, cited "CDNT p.N" (PDF pages).

Theorem 1 (p.3) and Theorem 2 (Appendix, p.12, proved on pp.13–14), in the two-party qubit
protocol model of the frozen `TwoPartyProtocol` (p.13): Alice's `n` input qubits hold `|x⟩`, every
other wire starts in `|0⟩` except the wires of a shared state `Φ` (fixed before the input), and
each step is a unitary of one party on wires it holds or the sending of one qubit. Bob finally
measures a POVM acting on the wires he holds. `nAB` (`nBA`) counts the qubits Alice sends Bob
(Bob sends Alice). Mutual information is for `X` uniform on `{0,1}^n` (p.13), in bits.
`⌈k/2⌉` on naturals is `(k + 1) / 2`.
-/

namespace QAlgorithms.Papers.CDNT98

universe u

/-- CDNT, Theorem 1 (p.3; it follows from Theorem 2, p.12, by the remark after it).

For every valid two-party protocol on Alice's `n` input bits, with an arbitrary prior shared state
and arbitrary qubit communication from Bob to Alice:
1. if Bob's final measurement (outcome set `{0,1}^n`, acting on his qubits) returns `x` with
   probability `1` for every input `x` (Alice conveys her `n` bits), then Alice sends Bob at least
   `⌈n/2⌉` qubits;
2. for every measurement of Bob and every natural `m`, if the mutual information between the
   uniformly distributed `X` and Bob's outcome is at least `m` bits, then Alice sends Bob at least
   `⌈m/2⌉` qubits. -/
theorem convey_bits_needs_half_qubits {n : ℕ} (P : TwoPartyProtocol n) (hP : P.IsValid) :
    (∀ M : Qubits n → Matrix (Qubits P.N) (Qubits P.N) ℂ, P.IsBobMeasurement M →
        (∀ x : Qubits n, P.outcomeProb M x x = 1) → (n + 1) / 2 ≤ P.nAB) ∧
      (∀ (Y : Type u) [Fintype Y] (M : Y → Matrix (Qubits P.N) (Qubits P.N) ℂ),
        P.IsBobMeasurement M → ∀ m : ℕ, (m : ℝ) ≤ P.mutualInfo M → (m + 1) / 2 ≤ P.nAB) := by
  sorry

/-- CDNT, Theorem 2 (Appendix, p.12; proof pp.13–14), exact form.

With no prior entanglement (no shared wires: Alice starts with `|x⟩|0…0⟩`, Bob with `|0…0⟩`) and
qubit communication in both directions, there is a valid protocol in which Alice sends exactly
`a` qubits to Bob and Bob exactly `b` qubits to Alice, and a measurement of Bob that returns `x`
with probability `1` for every input `x`, if and only if `a ≥ ⌈n/2⌉` (28) and `a + b ≥ n` (29). -/
theorem capacity_region_exact (n a b : ℕ) :
    (∃ P : TwoPartyProtocol n, P.IsValid ∧ P.e = 0 ∧ P.nAB = a ∧ P.nBA = b ∧
        ∃ M : Qubits n → Matrix (Qubits P.N) (Qubits P.N) ℂ, P.IsBobMeasurement M ∧
          ∀ x : Qubits n, P.outcomeProb M x x = 1) ↔
      (n + 1) / 2 ≤ a ∧ n ≤ a + b := by
  sorry

/-- CDNT, Theorem 2 (Appendix, p.12; proof pp.13–14), mutual-information form.

For `m ≤ n` ("`m` bits of mutual information with respect to Alice's `n` bits"): with no prior
entanglement, there is a valid protocol with exactly `a` qubits from Alice to Bob and `b` from Bob
to Alice and a measurement of Bob whose outcome has mutual information at least `m` bits with
Alice's uniformly distributed input, if and only if `a ≥ ⌈m/2⌉` and `a + b ≥ m`. -/
theorem capacity_region_mutualInfo (n m a b : ℕ) (hm : m ≤ n) :
    (∃ P : TwoPartyProtocol n, P.IsValid ∧ P.e = 0 ∧ P.nAB = a ∧ P.nBA = b ∧
        ∃ (Y : Type) (_ : Fintype Y) (M : Y → Matrix (Qubits P.N) (Qubits P.N) ℂ),
          P.IsBobMeasurement M ∧ (m : ℝ) ≤ P.mutualInfo M) ↔
      (m + 1) / 2 ≤ a ∧ m ≤ a + b := by
  sorry

end QAlgorithms.Papers.CDNT98
