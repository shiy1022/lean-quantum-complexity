import QAlgorithms.Defs.Fourier

/-!
# de Wolf, Chapter 4: The Fourier Transform

R. de Wolf, *Quantum Computing: Lecture Notes*, §4.5 (efficient circuit for the QFT, PDF pp.44–45)
and §4.6 (phase estimation, PDF pp.45–46).
-/

namespace QAlgorithms.DeWolf

/-- de Wolf §4.5, PDF pp.44–45 (unnumbered): the `n`-qubit quantum Fourier transform `F_{2^n}`
(entries `ω_N^{jk}/√N`, `ω_N = e^{2πi/N}`, p.41; most significant bit first, p.44) is implemented
exactly by a circuit of Hadamards, controlled-`R_s` gates and swap gates with at most `n²` gates
("the overall circuit uses at most `n²` gates"), in particular `O(n²)` elementary gates. -/
theorem qft_circuit_exact (n : ℕ) :
    ∃ c : Circuit qftGateSet n, c.unitary = qftQubits n ∧ c.size ≤ n ^ 2 := by
  sorry

/-- de Wolf §4.6, PDF pp.45–46 (unnumbered): phase estimation in the exact case. Let `U` be a
unitary with eigenvector `ψ` (a unit vector), `U ψ = e^{2πiϕ} ψ`, `ϕ ∈ [0, 1)`, and suppose `ϕ`
has an exact `n`-bit expansion, `2^n ϕ = k ∈ ℕ`. Then after step 3 (applying `F_N`, `N = 2^n`, to
the first register of `|0^n⟩|ψ⟩` and then `|j⟩|ψ⟩ ↦ |j⟩ U^j |ψ⟩`) the state is
`F_N |2^n ϕ⟩ ⊗ |ψ⟩`, and after step 4 (`F_N^{-1} = F_N^*` on the first register) measuring the
first register yields `|2^n ϕ⟩ = |k⟩` with probability 1. -/
theorem phaseEstimation_exact {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (U : Matrix κ κ ℂ) (hU : U ∈ Matrix.unitaryGroup κ ℂ)
    (ψ : EuclideanSpace ℂ κ) (hψ : IsState ψ)
    (ϕ : ℝ) (hϕ0 : 0 ≤ ϕ) (hϕ1 : ϕ < 1)
    (heig : act U ψ = Complex.exp (2 * Real.pi * Complex.I * ϕ) • ψ)
    (k : ℕ) (hk : (2 : ℝ) ^ n * ϕ = k) :
    act (controlledPower n U * Matrix.kronecker (qftQubits n) (1 : Matrix κ κ ℂ))
        (tensorVec (zeroKet n) ψ) =
      tensorVec (act (qftQubits n) (ket (natToBits n k))) ψ ∧
    marginalFst (phaseEstimationState n U ψ) (natToBits n k) = 1 := by
  sorry

end QAlgorithms.DeWolf
