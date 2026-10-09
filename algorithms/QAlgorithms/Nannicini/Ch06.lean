import QAlgorithms.Defs.Adiabatic

/-!
# Nannicini, Chapter 6: Hamiltonian simulation

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages). The matrix exponential of Def. 6.3 (p.134) is Mathlib's power series
`NormedSpace.exp`. The source's 1-based clock index `j ∈ {1, …, N}` is `Fin N` (0-based): the
source's `|u^(1)⟩` is `ket 0` and `|u^(N)⟩` is `ket (N - 1)`.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.136, Proposition 6.9. Let `H_B` be the `N × N` clock Hamiltonian of p.135
(zero diagonal, `(H_B)_{j,j+1} = (H_B)_{j+1,j} = ½√(j(N−j))`, the frozen `clockHamiltonian N`)
and `M_s = Σ_j |u^(j)⟩⟨u^(N+1−j)|` the mirror matrix (`mirrorMatrix N`). For every orthonormal
eigenbasis `(ψ_j)` of `H_B` with eigenvalues `λ_j`, let `S` be the indices with `M_s ψ_j = ψ_j`
(symmetric). If a time `t` and an angle `ϕ` satisfy, for every `j` with `⟨ψ_j|u^(1)⟩ ≠ 0`,
`e^{−iλ_j t} = e^{iϕ}` when `j ∈ S` and `e^{−iλ_j t} = −e^{iϕ}` when `j ∉ S`, then
`e^{−iH_B t}|u^(1)⟩ = e^{iϕ}|u^(N)⟩`. -/
theorem clockHamiltonian_transport {N : ℕ} (hN : 0 < N)
    (ψ : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (lam : Fin N → ℝ)
    (heig : ∀ j, act (clockHamiltonian N) (ψ j) = (lam j : ℂ) • ψ j)
    (t ϕ : ℝ)
    (hphase : ∀ j, inner ℂ (ψ j) (ket (⟨0, hN⟩ : Fin N)) ≠ 0 →
      (act (mirrorMatrix N) (ψ j) = ψ j →
        Complex.exp (-(Complex.I * (lam j : ℂ) * (t : ℂ))) = Complex.exp ((ϕ : ℂ) * Complex.I)) ∧
      (act (mirrorMatrix N) (ψ j) ≠ ψ j →
        Complex.exp (-(Complex.I * (lam j : ℂ) * (t : ℂ))) = -Complex.exp ((ϕ : ℂ) * Complex.I))) :
    act (NormedSpace.exp (-(Complex.I * (t : ℂ)) • clockHamiltonian N)) (ket (⟨0, hN⟩ : Fin N)) =
      Complex.exp ((ϕ : ℂ) * Complex.I) • ket (⟨N - 1, by omega⟩ : Fin N) := by
  sorry

/-- Nannicini p.137, Proposition 6.12. For any unitary `U` and Hamiltonian `H` (a Hermitian
`2^n × 2^n` matrix, Def. 6.1) and any real time `t`, `e^{iUHU†t} = U e^{iHt} U†`. -/
theorem exp_unitary_conj {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (H : Matrix (Qubits n) (Qubits n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • (U * H * star U)) =
      U * NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * star U := by
  sorry

end QAlgorithms.Nannicini
