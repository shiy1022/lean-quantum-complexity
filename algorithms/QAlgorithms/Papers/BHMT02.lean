import QAlgorithms.Defs.PhaseOracles

/-!
# Brassard, Høyer, Mosca, Tapp: Quantum amplitude amplification and estimation

G. Brassard, P. Høyer, M. Mosca, A. Tapp, *Quantum amplitude amplification and estimation*
(arXiv:quant-ph/0005055v1), cited "BHMT p.N" (PDF pages).

The phase state `|S_M(ω)⟩` of Definition 8 is the frozen `bhmtPhaseState M ω` on the
`M`-dimensional register `Fin M`; the circle distance `d(ω0, ω1) = min_{z ∈ ℤ} |z + ω1 − ω0|` of
Definition 9 is the frozen `circDist ω0 ω1 = |(ω0 − ω1) − round (ω0 − ω1)|` (the minimum is
attained at `z = round (ω0 − ω1)`).
-/

namespace QAlgorithms.Papers.BHMT02

/-- BHMT p.16, Lemma 10: for `0 ≤ ω0, ω1 < 1` and `∆ = d(ω0, ω1)`, if `∆ = 0` then
`|⟨S_M(ω0)|S_M(ω1)⟩|² = 1`, and otherwise
`|⟨S_M(ω0)|S_M(ω1)⟩|² = sin²(M∆π) / (M² sin²(∆π))`. The integer `M > 0` is the standing
assumption of Definition 8. -/
theorem phaseState_overlap (M : ℕ) (hM : 0 < M) (ω0 ω1 : ℝ) (h0 : 0 ≤ ω0) (h0' : ω0 < 1)
    (h1 : 0 ≤ ω1) (h1' : ω1 < 1) :
    (circDist ω0 ω1 = 0 →
      ‖inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1)‖ ^ 2 = 1) ∧
    (circDist ω0 ω1 ≠ 0 →
      ‖inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1)‖ ^ 2 =
        Real.sin ((M : ℝ) * circDist ω0 ω1 * Real.pi) ^ 2 /
          ((M : ℝ) ^ 2 * Real.sin (circDist ω0 ω1 * Real.pi) ^ 2)) := by
  sorry

end QAlgorithms.Papers.BHMT02
