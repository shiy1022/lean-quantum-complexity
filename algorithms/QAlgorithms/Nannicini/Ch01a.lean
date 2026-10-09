import QAlgorithms.Defs.Measurement

/-!
# Nannicini, Chapter 1 (part a): model of computation

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Proposition 1.4 (p.9), Proposition 1.19 (p.14), Proposition 1.27 (p.19),
Theorem 1.32 (p.23), Proposition 1.37 (p.24).

The source's tensor product on `ℂ^m` with the standard basis is the Kronecker product (Def. 1.2):
for matrices it is `Matrix.kronecker`, for vectors `tensorVec`; the index type
`Fin m × Fin n` in lexicographic order is the Kronecker block order.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.9, Proposition 1.4: algebraic properties of the tensor (Kronecker) product.
For `A, B ∈ ℂ^{m×m}`, `C, D ∈ ℂ^{n×n}`, `u, v ∈ ℂ^m`, `w, x ∈ ℂ^n`, `a, b ∈ ℂ`:
(i) `(A ⊗ C)(B ⊗ D) = AB ⊗ CD`; (ii) `(A ⊗ C)(u ⊗ w) = Au ⊗ Cw`;
(iii) `(u + v) ⊗ w = u ⊗ w + v ⊗ w`; (iv) `u ⊗ (w + x) = u ⊗ w + u ⊗ x`;
(v) `(au) ⊗ (bw) = ab (u ⊗ w)`; (vi) `(A ⊗ C)† = A† ⊗ C†`. -/
theorem tensor_properties {m n : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (C D : Matrix (Fin n) (Fin n) ℂ) (u v : EuclideanSpace ℂ (Fin m))
    (w x : EuclideanSpace ℂ (Fin n)) (a b : ℂ) :
    Matrix.kronecker A C * Matrix.kronecker B D = Matrix.kronecker (A * B) (C * D) ∧
    act (Matrix.kronecker A C) (tensorVec u w) = tensorVec (act A u) (act C w) ∧
    tensorVec (u + v) w = tensorVec u w + tensorVec v w ∧
    tensorVec u (w + x) = tensorVec u w + tensorVec u x ∧
    tensorVec (a • u) (b • w) = (a * b) • tensorVec u w ∧
    (Matrix.kronecker A C).conjTranspose =
      Matrix.kronecker A.conjTranspose C.conjTranspose := by
  sorry

/-- Nannicini p.14, Proposition 1.19: a `q`-qubit register, `q > 1`, is in a basis state
(Def. 1.16: `|ψ⟩ = α_k |k⟩` with `|α_k|² = 1`) if and only if its state is the tensor product
`|ψ_1⟩ ⊗ ⋯ ⊗ |ψ_q⟩` of `q` single-qubit states each of which is a basis state. Wire `i` is the
source's qubit `i + 1` (the first qubit is the most significant). -/
theorem basisState_iff_prod_basisStates {q : ℕ} (hq : 1 < q)
    (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ) :
    IsBasisState ψ ↔ ∃ φ : Fin q → EuclideanSpace ℂ Bool,
      (∀ i, IsState (φ i) ∧ IsBasisState (φ i)) ∧ ψ = prodState φ := by
  sorry

/-- Nannicini p.19, Proposition 1.27: for a `q`-qubit state `|ψ⟩ = ∑_j α_j |j⟩`, measuring the
`q` qubits one at a time with the single-qubit measurement gate of Postulate 3 (outcome
probability, then collapse and renormalization), in any order, yields the string `j` with
probability `|α_j|²`. The order is a permutation `σ` of the qubits: qubit `σ 0` is measured
first, then `σ 1`, and so on. -/
theorem seqMeasProb_eq_prob {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ)
    (σ : Equiv.Perm (Fin q)) (j : Qubits q) :
    seqMeasProb ψ (List.ofFn fun i => σ i) j = prob ψ j := by
  sorry

/-- Nannicini p.23, Theorem 1.32 (No-cloning principle): there is no unitary matrix on two
`q`-qubit registers that maps `|ψ⟩_q |0⟩_q` to `|ψ⟩_q |ψ⟩_q` for every `q`-qubit quantum state
`|ψ⟩`. -/
theorem no_cloning (q : ℕ) :
    ¬ ∃ U : Matrix (Qubits q × Qubits q) (Qubits q × Qubits q) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits q × Qubits q) ℂ ∧
      ∀ ψ : EuclideanSpace ℂ (Qubits q), IsState ψ →
        act U (tensorVec ψ (zeroKet q)) = tensorVec ψ ψ := by
  sorry

/-- Nannicini p.24, Proposition 1.37: the four Pauli gates `I, X, Y, Z` (Def. 1.36) form a basis
of `ℂ^{2×2}`, each is Hermitian, and `XYZ = iI`. -/
theorem pauli_basis_hermitian_xyz :
    LinearIndependent ℂ ![(1 : Matrix Bool Bool ℂ), pauliX, pauliY, pauliZ] ∧
    Submodule.span ℂ (Set.range ![(1 : Matrix Bool Bool ℂ), pauliX, pauliY, pauliZ]) = ⊤ ∧
    (1 : Matrix Bool Bool ℂ).IsHermitian ∧ pauliX.IsHermitian ∧ pauliY.IsHermitian ∧
    pauliZ.IsHermitian ∧
    pauliX * pauliY * pauliZ = Complex.I • (1 : Matrix Bool Bool ℂ) := by
  sorry

end QAlgorithms.Nannicini
