import QAlgorithms.Defs.Hamiltonian

/-!
# Childs, Chapter 31: Adiabatic optimization

A. Childs, *Lecture Notes on Quantum Algorithms*, §31.1–31.2 (PDF pp.165–166).

The problem Hamiltonian (31.2) is `problemHamiltonian h = Σ_z h(z)|z⟩⟨z|` on `n` qubits, the
linear interpolation (31.3) with `f(s) = s` is `linInterp HB HP s = (1 − s) HB + s HP`, the gap
`∆(s)` is `spectralGap (H s)` and `∆min` (31.8) is `minGap H`, the infimum of the gap over
`[0, 1]`. Operator norms are spectral norms (`specNorm`). The evolution (30.5)
`i dψ/ds = T H(s) ψ(s)` is `SolvesScaledSchrodinger H T ψ`.
-/

namespace QAlgorithms.Childs

/-- Childs, Theorem 31.1 (PDF p.166, eq. (31.9)): the running time of adiabatic optimization with
linear interpolation, in terms of the minimum gap. There are constants `c₁, c₃ > 0` (those of the
perturbation bounds (30.46)–(30.47), PDF p.162, introduced there as "some constants"; absolute,
so quantified before `n`, `h` and `H_B`) such that the following holds. Let `h : {0,1}ⁿ → ℝ`,
`H_P = Σ_z h(z)|z⟩⟨z|`, and let `H_B` be a beginning Hamiltonian on `n` qubits such that
`H(s) = (1 − s) H_B + s H_P` has a nondegenerate ground state for every `s ∈ [0, 1]` (the standing
assumption of §31.1, PDF p.166; it makes every `H(s)`, in particular `H_B = H(0)`, Hermitian).
Let `ϵ > 0` and
`T ≥ (2/ϵ)(2c₁‖H_P − H_B‖/∆min² + (3c₁² + c₁ + c₃)‖H_P − H_B‖²/∆min³)`. If `ψ` solves
`i dψ/ds = T H(s) ψ(s)` on `[0, 1]` with `ψ(0)` a unit ground state of `H_B`, then
`‖ψ(1) − ϕ(1)‖ ≤ ϵ` for a unit ground state `ϕ(1)` of `H_P` (the ground state is fixed only up to a
phase, PDF p.160, so the conclusion asserts some unit ground state). -/
theorem adiabatic_running_time_gap :
    ∃ c1 c3 : ℝ, 0 < c1 ∧ 0 < c3 ∧
      ∀ (n : ℕ) (h : Qubits n → ℝ) (HB : Matrix (Qubits n) (Qubits n) ℂ),
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasSimpleGroundState (linInterp HB (problemHamiltonian h) s)) →
        ∀ ε : ℝ, 0 < ε →
        ∀ T : ℝ,
          T ≥ 2 / ε * (2 * c1 * specNorm (problemHamiltonian h - HB) /
              minGap (linInterp HB (problemHamiltonian h)) ^ 2 +
            (3 * c1 ^ 2 + c1 + c3) * specNorm (problemHamiltonian h - HB) ^ 2 /
              minGap (linInterp HB (problemHamiltonian h)) ^ 3) →
        ∀ ψ : ℝ → EuclideanSpace ℂ (Qubits n),
          SolvesScaledSchrodinger (linInterp HB (problemHamiltonian h)) T ψ →
          IsGroundState HB (ψ 0) →
          ∃ φ1 : EuclideanSpace ℂ (Qubits n),
            IsGroundState (problemHamiltonian h) φ1 ∧ ‖ψ 1 - φ1‖ ≤ ε := by
  sorry

end QAlgorithms.Childs
