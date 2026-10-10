import QAlgorithms.Defs.QAOA

/-!
# Farhi–Goldstone–Gutmann, *A quantum approximate optimization algorithm applied to a bounded
occurrence constraint problem* (arXiv:1412.6062v2)

Cited "FGG-E3LIN2 p.N" (PDF pages). The p = 1 QAOA state is
`|γ, β⟩ = e^{−iβB} e^{−iγC} |s⟩` (eq. (4), p.2), with `C` the diagonal operator counting satisfied
equations (eq. (1)), `B = X_1 + ⋯ + X_n` (eq. (2)) and `|s⟩ = |+⟩^{⊗n}` (eq. (3)); this is the
frozen `qaoaUnitary` with `p = 1` applied to `H^{⊗n}|0⟩`, and its expected measured objective is
`qaoaExpectation`.
-/

namespace QAlgorithms.Papers.FGG14b

open QAlgorithms

/-- FGG-E3LIN2 §II, main result (pp.3–4, conclusion (43)–(45), pp.8–9; v2 bound): for large `D`,
for every Max E3LIN2 instance with `m` equations (exactly three distinct variables each, at most
one equation per variable triple, eq. (6)) in which every bit occurs in at most `D + 1` equations
(p.3, p.5), there is `γ ∈ [−1/(10 D^{1/2}), 1/(10 D^{1/2})]` such that, with `β = π/4`, the
expected number of satisfied equations in the measured p = 1 QAOA state `|γ, π/4⟩` is at least
`(1/2 + 1/(101 D^{1/2} ln D)) m`. -/
theorem qaoa1_e3lin2_bound :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ (n : ℕ) (I : E3LIN2Instance n), I.OccurrenceAtMost (D + 1) →
      ∃ γ : ℝ, |γ| ≤ 1 / (10 * Real.sqrt D) ∧
        (1 / 2 + 1 / (101 * Real.sqrt D * Real.log D)) * (I.eqs.card : ℝ) ≤
          qaoaExpectation (fun z => (I.numSatisfied z : ℝ)) 1 (fun _ => Real.pi / 4)
            (fun _ => γ) := by
  sorry

end QAlgorithms.Papers.FGG14b
