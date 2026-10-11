import QAlgorithms.Defs.DQI

/-!
# Jordan, Shutty, Wootters, Zalcman, Schmidhuber, King, Isakov, Khattar, Babbush,
*Optimization by decoded quantum interferometry* (arXiv:2408.08292v5)

Cited "DQI p.N" (PDF pages). A max-LINSAT instance (Definition 2.1, p.4) is a matrix
`B ∈ F_p^{m×n}` and sets `F_i ⊆ F_p`; constraint `i` is `b_i · x ∈ F_i`, and
`f_i = +1` exactly on `F_i` (§8.2.1, p.21), so `f(x) = Σ_i f_i(b_i · x)` is the frozen
`linsatObjective`. The DQI state `|P(f)⟩ = Σ_x P(f(x)) |x⟩` (eq. (8), p.11) is the frozen
`dqiState`, normalized to unit norm (p.21, Lemma 9.2 p.26), and the optimum over degree-`ℓ`
polynomials of the expected number of satisfied constraints is the frozen `dqiOptimalSatisfied`.
-/

namespace QAlgorithms.Papers.DQI24

open QAlgorithms

/-- DQI Theorem 4.1 (p.11; proof §9.4, p.34): let `p` be prime and `r ∈ {1, …, p − 1}`, and fix
`μ = ℓ/m`. For max-LINSAT instances `B ∈ F_p^{m×n}`, `F_1, …, F_m ⊆ F_p` with `|F_i| = r` for
all `i`, `m > n` (Lemma 9.2, p.26, on which the proof rests), and
`2ℓ + 1 < d⊥` (every nonzero `d ∈ F_p^m` with `Bᵀ d = 0` has Hamming weight `> 2ℓ + 1`), the
optimal expected number `⟨s⟩_opt` of satisfied constraints over unit-norm DQI states `|P(f)⟩` with
`deg P ≤ ℓ` satisfies, in the limit `m → ∞` with `ℓ/m = μ` fixed,
`⟨s⟩_opt / m → (√(μ(1 − r/p)) + √((r/p)(1 − μ)))²` if `r/p ≤ 1 − μ`, and `→ 1` otherwise.
The limit is stated uniformly: for every `ε > 0` there is `M` such that every such instance
with `m ≥ M` is within `ε` of the limit value. -/
theorem dqi_semicircle_law (p : ℕ) [Fact p.Prime] (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < p) (μ : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
      (F : Fin m → Finset (ZMod p)) (ℓ : ℕ),
      M ≤ m → n < m → (ℓ : ℝ) = μ * m → (∀ i, (F i).card = r) →
      DualDistanceExceeds B (2 * ℓ + 1) →
      |dqiOptimalSatisfied B F ℓ / m - semicircleValue μ ((r : ℝ) / p)| ≤ ε := by
  sorry

end QAlgorithms.Papers.DQI24
