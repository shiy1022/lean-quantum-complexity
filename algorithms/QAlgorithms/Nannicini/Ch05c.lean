import QAlgorithms.Defs.GradientMethods

/-!
# Nannicini, Chapter 5 (part c): encoding an arbitrary vector in a quantum state

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §5.2: Proposition 5.36 (p.125) and Corollary 5.37 (p.126).
Theorem 5.33 (p.123) and Corollary 5.45 (p.130) are not stated (see `HARD.md`).

Conventions. The amplitude encoding `|amp(x)⟩ = ∑_j x_j/‖x‖ |j⟩` on `n = ⌈log d⌉` qubits
(Def. 5.34) is `padState n (normalizedVec x)`, the index `j` being read from the qubits most
significant bit first (`bitsToNat`). Algorithm 4 (p.126) is the frozen `alg4Unitary`: the binary
tree values `N(k, j)` are `ampTreeValue`, line 2 and line 5 are the steps `alg4Step n x k`
(`k = 0` is the initialization `|ψ₁⟩`, wire `k` is the fresh qubit of iteration `k`, controlled
by the first `k` wires), and line 7 is the sign diagonal with `sign(x_j) = −1` if `x_j < 0` and
`+1` otherwise.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.125, Proposition 5.36: "Alg. 4 returns a quantum circuit on n qubits mapping
`|0⟩` to `|amp(x)⟩`."

Standing assumptions of §5.2 (p.124) and Alg. 4 (p.126): `d = 2^n`, `x ∈ ℝ^d` with `‖x‖ = 1`;
`n ≥ 1` because the initialization (line 2) reads the level-1 nodes `N(1, 0)`, `N(1, 1)` of the
tree. The conclusion: the operator produced by Alg. 4 is unitary (a quantum circuit) and maps
`|0…0⟩` to `|amp(x)⟩`. -/
theorem alg4_prepares_ampEncoding (n : ℕ) (hn : 1 ≤ n) (x : Fin (2 ^ n) → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) :
    alg4Unitary n x ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧
      act (alg4Unitary n x) (zeroKet n) =
        padState n (normalizedVec (WithLp.toLp 2 fun j => (x j : ℂ))) := by
  sorry

/-- Nannicini p.126, Corollary 5.37: "Given a classical description of `x ∈ ℂ^d` in finite
precision, there is a circuit that implements the mapping `|0⟩ → |amp(x)⟩` with error at most
`ϵ` with gate complexity `Õ(d)`."

The circuit is built from the classical data `x` (Rem. 5.35), over the gate set `{H, T, CX}` of
Thm. 1.43, on the `n = ⌈log d⌉` qubits of `|amp(x)⟩` plus `w` ancillas that start in `|0⟩`.
"Error at most `ϵ`" is the Euclidean distance between the produced state and
`|amp(x)⟩ ⊗ |0^w⟩` (§1.3.6). `Õ(d)` with the dependence on `ϵ` polylogarithmic (p.127) is
`C · d · (log(2 + d) + log(2 + 1/ϵ))^c` with constants `C > 0`, `c` chosen before `d`, `x`, `ϵ`.
The statement is for every nonzero `x ∈ ℂ^d`, which contains every finite-precision input. -/
theorem ampEncoding_gateComplexity :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (d : ℕ) (x : Fin d → ℂ), x ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ (w : ℕ) (circ : Circuit htcxGateSet (Nat.clog 2 d + w)),
        (circ.size : ℝ) ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        ‖act circ.unitary (zeroKet (Nat.clog 2 d + w)) -
            WithLp.toLp 2 (fun z : Qubits (Nat.clog 2 d + w) =>
              if ∀ k : Fin w, z (Fin.natAdd (Nat.clog 2 d) k) = false then
                padState (Nat.clog 2 d) (normalizedVec (WithLp.toLp 2 x))
                  (fun i => z (Fin.castAdd w i))
              else 0)‖ ≤ ε := by
  sorry

end QAlgorithms.Nannicini
