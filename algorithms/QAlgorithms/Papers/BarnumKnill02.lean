import QAlgorithms.Defs.QuantumInformation

/-!
# Barnum–Knill, *Reversing quantum dynamics with near-optimal quantum and classical fidelity*

H. Barnum, E. Knill, arXiv:quant-ph/0004088v2, cited "Barnum–Knill p.N" (PDF pages).

Theorem 5 (§VI, p.11, Eq. (39)), stated on the ensemble `{p_j, ρ̂_j}` of §V (p.10): for a map `A`
of the form (35) the classical fidelities of reversal are success probabilities of measurements
discriminating the `ρ̂_j`, and the near-optimal reversal `R_{A,ρ}` is the pretty good measurement
`X_j = ρ_out^{-1/2} ρ_j ρ_out^{-1/2}` (Eq. (37)), `ρ_j = p_j ρ̂_j`, `ρ_out = Σ_j ρ_j`, with the
generalized inverse of p.7.
-/

namespace QAlgorithms.Papers.BarnumKnill02

/-- Barnum–Knill, Theorem 5 (p.11, Eq. (39), with Eq. (38) and the proof on pp.12–13).

For an ensemble `{p_j, ρ̂_j}` of density matrices with probabilities `p_j` (finitely many labels,
finite dimension), the success probability of the pretty good measurement,
`Σ_j tr(ρ_out^{-1/2} ρ_j ρ_out^{-1/2} ρ_j)` (`mixedPgmSuccess`), and hence the optimal success
probability over all measurements with outcome set the labels (`mixedOptSuccess`), are at least
`1 − Σ_{i ≠ j} √(p_i p_j) F_BU(ρ̂_i, ρ̂_j)`, where `F_BU(σ₁, σ₂) = tr √(σ₁^{1/2} σ₂ σ₁^{1/2})`
(`rootFidelity`).

The paper writes the left side of (39) as `F_cl^2`; its own proof bounds `F_cl(ρ, R_{A,ρ}A)` (the
PGM success probability) and then the optimal `F_cl ≥ F_cl(ρ, R_{A,ρ}A)`, which is what is stated
here (the squared form contradicts Corollary 4 and is false in general). -/
theorem pgm_success_ge_one_sub_sum_bures {O ι : Type*} [Fintype O] [DecidableEq O] [Fintype ι]
    [DecidableEq ι] (p : O → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (ρh : O → Matrix ι ι ℂ) (hρ : ∀ j, IsDensityMatrix (ρh j)) :
    1 - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) ≤
        mixedPgmSuccess p ρh ∧
      1 - ∑ i, ∑ j ∈ Finset.univ.erase i, Real.sqrt (p i * p j) * rootFidelity (ρh i) (ρh j) ≤
        mixedOptSuccess p ρh := by
  sorry

end QAlgorithms.Papers.BarnumKnill02
