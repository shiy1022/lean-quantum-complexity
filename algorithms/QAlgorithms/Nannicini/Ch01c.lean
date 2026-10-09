import QAlgorithms.Defs.Measurement

/-!
# Nannicini, Chapter 1 (§1.3.7, §1.4): implicit measurement, density matrices,
reduced density matrices, Schmidt decomposition

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages). A composite register `AB` is indexed by `Qubits ma × Qubits mb`, register `A` first.
-/

namespace QAlgorithms.Nannicini

open QAlgorithms

open scoped ComplexOrder

/-- Nannicini p.32, Proposition 1.50 (principle of implicit measurement), in the form of the
consistency claim argued right after it: measuring the qubits `l` one at a time (Post. 3,
Prop. 1.27) gives outcome `y` on `l` with the same probability as measuring the qubits `l`
and then further, never-measured qubits `r`, and discarding the outcomes on `r` (summing over
them). The state `ψ` is a unit vector. -/
theorem implicitMeasurement {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ)
    (l r : List (Fin q)) (hlr : (l ++ r).Nodup) (y : Qubits q) :
    seqMeasProb ψ l y =
      ∑ z ∈ Finset.univ.filter (fun z : Qubits q => ∀ i, i ∉ r → z i = y i),
        seqMeasProb ψ (l ++ r) z := by sorry

/-- Nannicini p.36, Theorem 1.60 (characterization of density matrices): a `q`-qubit matrix `ρ`
is the density matrix `∑_j p_j |ψ_j⟩⟨ψ_j|` of some ensemble `{p_j, |ψ_j⟩}_{j=1..m}` of pure
states (unit vectors) with probabilities `p_j ≥ 0`, `∑_j p_j = 1`, for some `m`, if and only if
`ρ` has unit trace and is positive semidefinite. -/
theorem densityMatrix_iff {q : ℕ} (ρ : Matrix (Qubits q) (Qubits q) ℂ) :
    (∃ (m : ℕ) (p : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℂ (Qubits q)),
        (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧ (∀ j, IsState (ψ j)) ∧ ρ = ensembleDensity p ψ) ↔
      ρ.trace = 1 ∧ ρ.PosSemidef := by sorry

/-- Nannicini p.39, Proposition 1.67: if the register `AB` (`A` of `ma` qubits first, `B` of
`mb` qubits) is in the mixed state `ρ^{(AB)}`, then the reduced density matrix
`ρ^{(A)} = Tr_B ρ^{(AB)}` gives, for every outcome `j ∈ {0,1}^{ma}`, the probability
`⟨j|ρ^{(A)}|j⟩` equal to the probability `∑_k ⟨j|⟨k|ρ^{(AB)}|j⟩|k⟩` of observing `j` on `A`
when all qubits of `AB` are measured and the outcome on `B` is discarded (Rem. 1.59). -/
theorem reducedDensity_prob {ma mb : ℕ}
    (ρ : Matrix (Qubits ma × Qubits mb) (Qubits ma × Qubits mb) ℂ) (hρ : IsDensityMatrix ρ)
    (j : Qubits ma) :
    densityProb (traceRight ρ) j = ∑ k : Qubits mb, densityProb ρ (j, k) := by sorry

/-- Nannicini p.40, Theorem 1.70 (Schmidt decomposition): every pure state `|ψ⟩` of a composite
register `AB` can be written `|ψ⟩ = ∑_j λ_j |φ_j^A⟩|φ_j^B⟩` with orthonormal states `φ_j^A` of
`A`, orthonormal states `φ_j^B` of `B`, and nonnegative reals `λ_j` with `∑_j λ_j² = 1`. The
index set of `j`, left unspecified by the source, is a finite `Fin r`. -/
theorem schmidtDecomposition {ma mb : ℕ} (ψ : EuclideanSpace ℂ (Qubits ma × Qubits mb))
    (hψ : IsState ψ) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (φA : Fin r → EuclideanSpace ℂ (Qubits ma))
      (φB : Fin r → EuclideanSpace ℂ (Qubits mb)),
      Orthonormal ℂ φA ∧ Orthonormal ℂ φB ∧ (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j ^ 2 = 1 ∧
        ψ = ∑ j, (lam j : ℂ) • tensorVec (φA j) (φB j) := by sorry

end QAlgorithms.Nannicini
