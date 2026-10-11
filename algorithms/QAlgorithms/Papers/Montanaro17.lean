import QAlgorithms.Defs.StabilizerLearning

/-!
# A. Montanaro, *Learning stabilizer states by Bell sampling* (arXiv:1707.04012v2)

Cited "Montanaro p.N" (PDF pages). A stabilizer state of `n` qubits (p.2: a unit vector fixed by
a commuting subgroup `G` of Pauli matrices with phases `±1`, `|G| = 2^n`) is the frozen
`IsStabilizerState`. A learner is the frozen `CopyLearner`: rounds that each consume fresh copies
of `|ψ⟩` and `|0⟩` ancillas, apply an `{H, T, CNOT}` circuit whose gates are classically
controlled by Boolean-circuit functions of the earlier outcomes, and measure everything in the
computational basis; a final Boolean circuit outputs a stabilizer tableau. The learner is fixed
before `ψ` (trap Q2). Time counts quantum gates, ancillas and classical Boolean gates.
-/

namespace QAlgorithms.Papers.Montanaro17

open QAlgorithms

/-- Montanaro Theorem 1 (p.1; Algorithm 1 and its analysis, p.2). There is a quantum algorithm
which identifies an unknown stabilizer state `|ψ⟩` of `n` qubits given access to `O(n)` copies of
`|ψ⟩`; it makes collective measurements across at most two copies at a time, runs in time
`O(n³)` and fails with probability exponentially small in `n`.

Formalized: there are constants `C > 0`, `c > 0` and a threshold `N₀` such that for every
`n ≥ N₀` there is one learner `L` (chosen before the state) in which every round uses at most two
copies, the total number of copies is at most `C n`, the time is at most `C n³`, and for every
`n`-qubit stabilizer state `ψ` the learner outputs a tableau whose stabilizer projector is
`|ψ⟩⟨ψ|` (identification up to global phase, p.2) with probability at least `1 − e^{−cn}`.
(The proof gives `5n + 2` copies and failure probability `≤ 2^{−n}`, p.2.) -/
theorem bell_sampling_learns_stabilizer_states :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ L : CopyLearner n,
        (∀ k, L.copies k ≤ 2) ∧
        (L.copiesUsed : ℝ) ≤ C * n ∧
        (L.time : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
        ∀ ψ : EuclideanSpace ℂ (Qubits n), IsStabilizerState ψ →
          L.successProb ψ ≥ 1 - Real.exp (-(c * n)) := by
  sorry

end QAlgorithms.Papers.Montanaro17
