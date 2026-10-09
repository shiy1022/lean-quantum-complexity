import QAlgorithms.Defs.Hamiltonian

/-!
# Childs, Chapter 30: The quantum adiabatic theorem

A. Childs, *Lecture Notes on Quantum Algorithms*, §30.1–30.2 (PDF pp.159–163).

The interpolating Hamiltonian is `H : ℝ → Matrix ι ι ℂ`, read on `s ∈ [0, 1]`. Its first and
second derivatives `Ḣ, Ḧ` are carried as functions `H1, H2` with derivative hypotheses within
`[0, 1]` (one-sided at the endpoints) and `H2` continuous, i.e. `H` is `C²` on `[0, 1]`; the proof
differentiates `H` twice. Operator norms are spectral norms (`specNorm`); the gap `∆(s)` is
`spectralGap (H s)`, which under a nondegenerate ground state is the distance from the smallest
eigenvalue to the nearest distinct one (PDF p.162). The Schrödinger equation (30.5)
`i dψ/ds = T H(s) ψ(s)` is `SolvesScaledSchrodinger H T ψ`.
-/

namespace QAlgorithms.Childs

/-- Childs, Theorem 30.1 (PDF p.163, eq. (30.49)–(30.50)): the quantitative adiabatic theorem.
There are constants `c₁, c₂, c₃` (those of the perturbation bounds (30.46)–(30.47), PDF p.162;
absolute, so quantified before the dimension and the Hamiltonian) such that the following holds.
Let `H(s)`, `s ∈ [0, 1]`, be a twice continuously differentiable family of Hermitian operators
with a nondegenerate ground state for every `s ∈ [0, 1]` (gap `∆(s) > 0`), let `ϵ > 0` and
`T ≥ (2/ϵ)[c₁‖Ḣ(0)‖/∆(0)² + c₁‖Ḣ(1)‖/∆(1)² + ∫₀¹ ((3c₁² + c₁ + c₃)‖Ḣ‖²/∆³ + c₂‖Ḧ‖/∆²) ds]`.
If `ψ` solves `i dψ/ds = T H(s) ψ(s)` on `[0, 1]` with `ψ(0)` a (unit) ground state of `H(0)`,
then `‖ψ(1) − ϕ(1)‖ ≤ ϵ` for a ground state `ϕ(1)` of `H(1)`; the instantaneous ground state is
fixed only up to a phase (PDF p.160), so the conclusion asserts some unit ground state of `H(1)`. -/
theorem adiabatic_theorem :
    ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H H1 H2 : ℝ → Matrix ι ι ℂ),
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasSimpleGroundState (H s)) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H (H1 s) (Set.Icc 0 1) s) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H1 (H2 s) (Set.Icc 0 1) s) →
        ContinuousOn H2 (Set.Icc 0 1) →
        ∀ ε : ℝ, 0 < ε →
        ∀ T : ℝ,
          T ≥ 2 / ε * (c1 * specNorm (H1 0) / spectralGap (H 0) ^ 2 +
            c1 * specNorm (H1 1) / spectralGap (H 1) ^ 2 +
            ∫ s in (0 : ℝ)..1,
              ((3 * c1 ^ 2 + c1 + c3) * specNorm (H1 s) ^ 2 / spectralGap (H s) ^ 3 +
                c2 * specNorm (H2 s) / spectralGap (H s) ^ 2)) →
        ∀ ψ : ℝ → EuclideanSpace ℂ ι,
          SolvesScaledSchrodinger H T ψ →
          IsGroundState (H 0) (ψ 0) →
          ∃ φ1 : EuclideanSpace ℂ ι, IsGroundState (H 1) φ1 ∧ ‖ψ 1 - φ1‖ ≤ ε := by
  sorry

end QAlgorithms.Childs
