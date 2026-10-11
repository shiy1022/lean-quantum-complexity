import QAlgorithms.Defs.SpectralFilter

/-!
# Lin–Tong, *Near-optimal ground state preparation* (arXiv:2002.12508v3)

Cited "LT-gs p.N" (PDF pages). Theorem 6 (p.7): ground state preparation with an a priori
ground energy bound.

Model (pp.2–3, 5–7).
* `H ∈ ℂ^{N×N}`, `N = 2^n`, Hermitian, eigenvalues `λ₀ ≤ λ₁ ≤ ⋯` (frozen `ascEigenvalues`,
  increasing, `minEigenvalue = λ₀`); a ground state `|ψ₀⟩` is a unit eigenvector for `λ₀`
  (frozen `IsGroundState`).
* `U_H` is an `(α, m, 0)`-block-encoding of `H` (Eq. (1), p.3: an `(m + n)`-qubit unitary with
  `‖H − α(⟨0^m| ⊗ I) U_H (|0^m⟩ ⊗ I)‖ = 0`, ancilla register first): the frozen
  `IsQubitBlockEncoding m n U_H α 0 H`.
* `U_I` is an `n`-qubit unitary with `U_I |0^n⟩ = |φ₀⟩` (p.6).
* Fidelity between states `|x⟩, |y⟩` is `|⟨x|y⟩|` (footnote 1, p.2).
* The algorithm is an oracle circuit over one- and two-qubit gates (frozen
  `oneTwoQubitGateSet`) with two oracles, oracle `0` = `U_H` (on `m + n` wires) and oracle `1` =
  `U_I` (on `n` wires); plain, adjoint and controlled applications are all counted (frozen
  `queryCount`).
-/

namespace QAlgorithms.Papers.LinTong20Ground

open QAlgorithms

/-- The pair of oracles of Theorem 6: index `0` is the block-encoding `U_H` (on `m + n` qubits),
index `1` the initial-state preparation `U_I` (on `n` qubits). -/
def oraclePair {m n : ℕ} (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ)
    (UI : Matrix (Qubits n) (Qubits n) ℂ) :
    (k : Fin 2) → Matrix (Qubits (![m + n, n] k)) (Qubits (![m + n, n] k)) ℂ
  | ⟨0, _⟩ => UH
  | ⟨1, _⟩ => UI

example {m n : ℕ} (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ)
    (UI : Matrix (Qubits n) (Qubits n) ℂ) : oraclePair UH UI 0 = UH ∧ oraclePair UH UI 1 = UI :=
  ⟨rfl, rfl⟩

/-- The (unnormalized) system state left on the first `n` wires of an `(n + w)`-qubit state `φ`
when the last `w` (ancilla) wires are measured with outcome `a`: `y ↦ φ(y, a)`. Its squared norm
is the probability of the ancilla outcome `a`. -/
noncomputable def ancillaBranch {n w : ℕ} (φ : EuclideanSpace ℂ (Qubits (n + w))) (a : Qubits w) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun y => φ (Fin.append y a)

/-- **LT-gs Theorem 6** (PDF p.7), ground state preparation with an a priori ground energy bound.

Suppose `H = Σ_k λ_k |ψ_k⟩⟨ψ_k| ∈ ℂ^{N×N}` (`λ_k ≤ λ_{k+1}`) is given through its
`(α, m, 0)`-block-encoding `U_H`, the initial state `|φ₀⟩` is prepared by `U_I`, and the promises
(P1) `|⟨φ₀|ψ₀⟩| ≥ γ` and (P2) `λ₀ ≤ μ − Δ/2 < μ + Δ/2 ≤ λ₁` hold. Then the ground state `|ψ₀⟩`
can be prepared to fidelity `1 − ε` with `O((α/(γΔ)) log(1/(γε)))` queries to `U_H`, `O(1/γ)`
queries to `U_I`, `O(n + m)` qubits and `O((mα/(γΔ)) log(1/(γε)))` other one- and two-qubit
gates.

Encoding choices.
* The circuit, its number `w` of ancillas and its success predicate `good` on ancilla outcomes are
  chosen from the known data `n, m, α, Δ, μ, γ, ε` only, before `H, U_H, U_I` (trap Q2; p.6:
  "for some known `γ > 0`, `μ`, and `Δ`"). It runs on `|0^{n+w}⟩`, system register the first `n`
  wires; the ancillas are measured, and outcome `a` with `good a` is success.
* "Prepared … with the following costs" is read through the proof (p.7: "the procedure succeeds
  with some constant probability"): one absolute constant `c > 0` lower-bounds the success
  probability, and on every successful outcome the post-measurement system state
  `v_a / ‖v_a‖` has fidelity `|⟨ψ₀|v_a⟩| / ‖v_a‖ ≥ 1 − ε` (stated without division).
* `O(·)` is one absolute constant `C`, quantified before everything (trap 8). The source's `O` is
  plain (its `Õ`, footnote 2, is not used in Theorem 6, and the proof gives no log factors).
* (P2) is stated without indexing `λ₁` directly: `λ₀ ≤ μ − Δ/2`, `Δ > 0`, and every eigenvalue of
  index `k ≥ 1` is `≥ μ + Δ/2`. (P1) uses the ground state `ψ₀` (unique up to phase under (P2), so
  the overlap and the fidelity do not depend on the choice). `0 < ε < 1` (fidelity `1 − ε`).
* The known parameters carry the constraints the instances force (so that the cost bounds, which
  are fixed before any instance, are not negative on parameter values that admit no instance):
  `0 ≤ α` (the block-encoding's normalization), `0 < γ ≤ 1` (an overlap of unit vectors, (P1)).
  With them `γε < 1`, so `log(1/(γε)) > 0`.

**Corrections** (trap 30). Printed: `O(n + m)` qubits and `O((mα/(γΔ)) log(1/(γε)))` gates.
Changed: `n + w ≤ C(n + m + 1)` and `(m + 1)` in place of `m`. Why: at `n = m = 0` the printed
qubit bound is `0`, and at `m = 0` the printed gate bound is `0`, while the construction needs
`m + 3` ancillas and Hadamard gates (the paper's own Theorem 1, p.3, gives `O((m + 1)ℓ)` gates). -/
theorem groundStatePrep_knownBound :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ) (α Δ μ γ ε : ℝ), 0 ≤ α → 0 < Δ → 0 < γ → γ ≤ 1 → 0 < ε → ε < 1 →
        ∃ (w : ℕ) (circ : OracleCircuit oneTwoQubitGateSet ![m + n, n] (n + w))
          (good : Qubits w → Bool),
          ((n + w : ℕ) : ℝ) ≤ C * ((n : ℝ) + m + 1) ∧
          (circ.queryCount 0 : ℝ) ≤ C * (α / (γ * Δ)) * Real.log (1 / (γ * ε)) ∧
          (circ.queryCount 1 : ℝ) ≤ C * (1 / γ) ∧
          (circ.gateCount : ℝ) ≤ C * ((m : ℝ) + 1) * (α / (γ * Δ)) * Real.log (1 / (γ * ε)) ∧
          ∀ (H : Matrix (Qubits n) (Qubits n) ℂ)
            (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ)
            (UI : Matrix (Qubits n) (Qubits n) ℂ) (ψ0 : EuclideanSpace ℂ (Qubits n)),
            H.IsHermitian → IsQubitBlockEncoding m n UH α 0 H →
            UI ∈ Matrix.unitaryGroup (Qubits n) ℂ →
            IsGroundState H ψ0 →
            -- (P1)
            γ ≤ ‖inner ℂ ψ0 (act UI (zeroKet n))‖ →
            -- (P2)
            minEigenvalue H ≤ μ - Δ / 2 →
            (∀ k : Fin (Fintype.card (Qubits n)), (k : ℕ) ≠ 0 → μ + Δ / 2 ≤ ascEigenvalues H k) →
            c ≤ probEvent (act (circ.unitary (oraclePair UH UI)) (zeroKet (n + w)))
                (fun z => good (qubitsAppendEquiv n w z).2 = true) ∧
              ∀ a : Qubits w, good a = true →
                (1 - ε) * ‖ancillaBranch (act (circ.unitary (oraclePair UH UI)) (zeroKet (n + w))) a‖ ≤
                  ‖inner ℂ ψ0
                    (ancillaBranch (act (circ.unitary (oraclePair UH UI)) (zeroKet (n + w))) a)‖ := by
  sorry

end QAlgorithms.Papers.LinTong20Ground
