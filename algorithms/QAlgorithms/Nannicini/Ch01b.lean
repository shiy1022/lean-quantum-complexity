import QAlgorithms.Defs.Adiabatic

/-!
# Nannicini, Chapter 1 (part b): basic operations, universality, dealing with errors

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), §1.3.4 and §1.3.6
(PDF pp. 24–32). Conventions are the frozen ones: an `q`-qubit register is indexed by
`Qubits q`, wire `i` is the source's qubit `i + 1`, and the first qubit is the most significant
bit.
-/

namespace QAlgorithms.Nannicini

open QAlgorithms

/-- Nannicini, Proposition 1.38, PDF p. 25. Given a `q`-qubit register in the state `|0⟩_q`,
applying the Hadamard gate to all qubits, or equivalently the matrix `H^{⊗q}` (Eq. (1.5)),
yields the uniform superposition `(1/√(2^q)) Σ_{j ∈ {0,1}^q} |j⟩`.

The first conjunct applies `H` to each wire in turn (wire `0` first); the second applies the
frozen `hadamardN q`, the matrix of Eq. (1.5). `uniformState (Qubits q)` has every amplitude
equal to `1/√(card (Qubits q)) = 1/√(2^q)`. -/
theorem hadamard_all_zero_uniform (q : ℕ) :
    act (orderedProd fun i : Fin q =>
        embedOp (Gate.ofMatrix1 hadamard).mat (Stabilizer.wire1 i)) (zeroKet q) =
      uniformState (Qubits q) ∧
    act (hadamardN q) (zeroKet q) = uniformState (Qubits q) := by
  sorry

/-- Nannicini, Proposition 1.41, PDF p. 27. The circuit of Fig. 1.13, made of three CX gates,
`CX₁₂ CX₂₁ CX₁₂`, swaps qubits 1 and 2: it equals the SWAP matrix of p. 27.

`cnot` is `CX₁₂` (control qubit 1, target qubit 2: `|x⟩|y⟩ ↦ |x⟩|y ⊕ x⟩`, p. 26);
`cnot.submatrix Prod.swap Prod.swap` is `CX₂₁` (control qubit 2, target qubit 1); `swapGate`
is the permutation matrix exchanging `|01⟩` and `|10⟩`. -/
theorem three_cnot_eq_swap :
    cnot * cnot.submatrix Prod.swap Prod.swap * cnot = swapGate := by
  sorry

/-- Nannicini, Proposition 1.46, PDF p. 31. Let `U_1 U_2 ⋯ U_T` and `U'_1 U'_2 ⋯ U'_T` be two
sequences of unitaries of the same length. Then
`‖U_1 U_2 ⋯ U_T − U'_1 U'_2 ⋯ U'_T‖ ≤ Σ_{j=1}^T ‖U_j − U'_j‖`, where `‖·‖` is the operator norm
induced by the Euclidean norm (Def. 1.35).

The unitaries act on `q` qubits (Postulate 2); the source's `U_j` is `U (j − 1)` and its
`U'_j` is `V (j − 1)`, and the products are taken in the source's left-to-right order,
`(List.ofFn U).prod = U 0 * ⋯ * U (T−1)`. At `T = 0` both products are `1` and the bound reads
`0 ≤ 0`. -/
theorem norm_prod_sub_prod_le_sum (q T : ℕ) (U V : Fin T → Matrix (Qubits q) (Qubits q) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Qubits q) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Qubits q) ℂ) :
    specNorm ((List.ofFn U).prod - (List.ofFn V).prod) ≤ ∑ j, specNorm (U j - V j) := by
  sorry

/-- Nannicini, Proposition 1.49, PDF pp. 31–32. Let `|ψ⟩ = Σ_j α_j |j⟩` and `|ϕ⟩ = Σ_j β_j |j⟩` be
two quantum states on `q` qubits, and let `P`, `Q` be the distributions over `{0,1}^q` obtained
by measuring all qubits (`P(j) = |α_j|²`, `Q(j) = |β_j|²`, Prop. 1.27). If
`‖|ψ⟩ − |ϕ⟩‖ ≤ ϵ`, then `d_TV(P, Q) ≤ ϵ`, with `d_TV(P, Q) = (1/2) Σ_j |p_j − q_j|`
(Def. 1.47). -/
theorem tvDist_le_of_norm_sub_le (q : ℕ) (ψ φ : EuclideanSpace ℂ (Qubits q))
    (hψ : IsState ψ) (hφ : IsState φ) (ε : ℝ) (h : ‖ψ - φ‖ ≤ ε) :
    tvDist (prob ψ) (prob φ) ≤ ε := by
  sorry

end QAlgorithms.Nannicini
