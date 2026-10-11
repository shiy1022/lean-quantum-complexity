import QAlgorithms.Defs.ApproxCounting

/-!
# Aaronson–Rall, *Quantum approximate counting, simplified* (arXiv:1908.10846v6)

Cited "AR p.N" (PDF pages). Theorem 1 (p.4), stated for the paper's own algorithm (pp.4, 8–9),
which the frozen layer `QAlgorithms.Defs.ApproxCounting` defines: the list is padded with
`10⁶ N` unmarked items, the only quantum operation is preparing `G^{(r−1)/2}|ψ⟩` with
`G = (I − 2|ψ⟩⟨ψ|)U` and measuring it, step 1 is the exponential search over
`r_k` = largest odd integer `≤ 1.05^k`, step 2 the rotation-lemma refinement, and the output is
`K̂ = N' sin²(θ_max)`. `acEventProb S ε δ E` is the probability that the run outputs `K̂` after
`q` queries with `E K̂ q`.
-/

namespace QAlgorithms.Papers.AaronsonRall20

open QAlgorithms
open scoped ENNReal

/-- AR p.4, Theorem 1 (approximate counting with Grover iterations only).

For the paper's algorithm on a nonempty marked set `S ⊆ [N]`, `K = |S|`, and any `ε, δ > 0`:
with probability at least `1 − δ` the output `K̂` satisfies `K(1 − ε) < K̂ < K(1 + ε)` and the
run made fewer than `Q(N, K, ε, δ)` queries, where `Q ∈ O(√(N/K) ε⁻¹ log δ⁻¹)` (as
`ε, δ → 0`, uniformly in `N` and `K`). The algorithm's register is the padded list
`[(10⁶ + 1) N]`, i.e. `O(log N)` qubits. -/
theorem approxCounting_groverOnly :
    ∃ Q : ℕ → ℕ → ℝ → ℝ → ℝ,
      (∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
        ∀ N K : ℕ, 1 ≤ K → K ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          Q N K ε δ ≤ C * Real.sqrt ((N : ℝ) / (K : ℝ)) * ε⁻¹ * Real.log δ⁻¹) ∧
      (∀ (N : ℕ) (S : Finset (Fin N)), S.Nonempty → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        ENNReal.ofReal (1 - δ) ≤ acEventProb S ε δ fun Khat q =>
          (S.card : ℝ) * (1 - ε) < Khat ∧ Khat < (S.card : ℝ) * (1 + ε) ∧
            (q : ℝ) < Q N S.card ε δ) ∧
      ∃ C : ℕ, ∀ N : ℕ, 2 ≤ N → Nat.clog 2 (acPadLen N) ≤ C * Nat.log 2 N := by
  sorry

end QAlgorithms.Papers.AaronsonRall20
