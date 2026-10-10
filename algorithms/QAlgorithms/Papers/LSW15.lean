import QAlgorithms.Defs.ConvexOpt

/-!
# Lee, Sidford, Wong: A faster cutting plane method

Y. T. Lee, A. Sidford, S. C. Wong, *A faster cutting plane method and its implications for
combinatorial and convex optimization* (arXiv:1508.04874v2), cited "LSW p.N" (PDF pages).

Objects (frozen definition layer): vectors of `ℝⁿ` are `Fin n → ℝ`; `MinWidth` (Definition 41,
p.54) is `minWidth`; an `(η, δ)`-separation oracle on a convex set `Γ` for `f` (Definition 2,
p.9) is `IsSeparationOracle η δ Γ f O`, where `O x = none` is the assertion
`f(x) ≤ min_{y∈Γ} f(y) + η` and `O x = some (c, b)` is the half space
`{z : cᵀz ≤ cᵀx + b}` with `c ≠ 0`, `b ≤ δ‖c‖₂`. A randomized algorithm calling the oracle is a
distribution (`PMF`) over deterministic adaptive strategies (`DecisionTree`) whose queries are
points of `ℝⁿ`, whose answers are oracle outputs and whose leaves are the returned points;
`expectedQueries` is its expected number of oracle calls. The box of radius `R` is
`B∞(R) = {x : ‖x‖_∞ ≤ R}` (§3.1, p.9).
-/

namespace QAlgorithms.Papers.LSW15

open scoped ENNReal

/-- LSW p.54, Theorem 42 (cited by Nannicini, Theorem 5.23): convex optimization from an
`(η, δ)`-separation oracle. Let `f` be a convex function on `ℝⁿ` and `Ω ⊆ B∞(R)` a convex set
containing a minimizer `x*` of `f`. For any `0 < α < 1` one can compute `x ∈ ℝⁿ` with
`f(x) − min_{y∈Ω} f(y) ≤ η + α (max_{y∈Ω} f(y) − min_{y∈Ω} f(y))` (10.1), using an expected
`O(n log(nκ/α))` calls of an `(η, δ)`-separation oracle defined on `B∞(R)`, where
`κ = R / MinWidth(Ω)` and `δ = Θ(α MinWidth(Ω) / (n^{3/2} log(nκ/α)))`.

Formalization choices.
* The algorithm `A` depends only on `n`, `R`, `α` and `w = MinWidth(Ω)` (the proof's stopping
  width (10.2) uses `MinWidth(Ω)`; p.55: "this algorithm requires no information about `Ω`
  (other than that `Ω ⊆ B∞(R)`)"), and is fixed before `η`, `f`, `Ω` and the oracle (trap Q2).
  The universal constants `c` (oracle accuracy) and `C` (call count) come before everything.
* Output guarantee on every run (every strategy in the support), call count in expectation.
* The oracle is any function meeting Definition 2 on `Γ = B∞(R)` ("we only need the oracle
  defined on the set `B∞(R)`"); its answers at points outside `B∞(R)` are unconstrained.
* `δ = Θ(…)` is read as: oracle accuracy `δ = c · α w / (n^{3/2} L)` suffices for a universal
  `c > 0` (a `δ'`-oracle with `δ' ≤ δ` is a `δ`-oracle).
* Discrepancy with the printed statement (trap 30): the theorem prints `ln(κ)` in `δ`, but the
  proof ((10.2) and "`δ = Ω(ε/√n)`") gives `ln(nκ/α)`, and `κ ≤ 1` is possible (`Ω = B∞(R)` has
  `κ = 1/2`), which would make the printed `δ` non-positive. We use
  `L = log(2 + nκ/α)` in both `δ` and the call bound; it agrees with `log(nκ/α)` up to universal
  constants whenever `nκ/α ≥ 2` and is always positive.
* Only the oracle part of the expected running time, `O(n · SO · log(nκ/α))`, is stated, as an
  expected number of oracle calls. The additional arithmetic time `n³ log^{O(1)}(nκ/α)` is
  **not stated**: the paper fixes no machine model for arithmetic on real vectors, so that clause
  cannot be pinned.
* `max_{y∈Ω} f(y)` is `sSup (f '' Ω)`: a finite convex function on `ℝⁿ` is continuous, hence
  bounded on the bounded set `Ω`, so this is the true supremum (attained on the closure).
  `min_{y∈Ω} f(y) = f(x*)` since `x* ∈ Ω` is a global minimizer.
* `n ≥ 1` and `0 < MinWidth(Ω)` are needed for `κ = R / MinWidth(Ω)` to be defined. -/
theorem convexOpt_of_separationOracle :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (R : ℝ), 0 < R → ∀ (α : ℝ), 0 < α → α < 1 → ∀ (w : ℝ), 0 < w →
        ∃ A : RandDecisionTree (Fin n → ℝ) (Option ((Fin n → ℝ) × ℝ)) (Fin n → ℝ),
          ∀ (η : ℝ), 0 ≤ η →
          ∀ (f : (Fin n → ℝ) → ℝ), ConvexOn ℝ Set.univ f →
          ∀ (Ω : Set (Fin n → ℝ)), Convex ℝ Ω → Ω ⊆ {x | ∀ i, |x i| ≤ R} → minWidth Ω = w →
          ∀ xstar ∈ Ω, (∀ y, f xstar ≤ f y) →
          ∀ (O : (Fin n → ℝ) → Option ((Fin n → ℝ) × ℝ)),
            IsSeparationOracle η
              (c * α * w / ((n : ℝ) * Real.sqrt n *
                Real.log (2 + (n : ℝ) * (R / w) / α)))
              {x | ∀ i, |x i| ≤ R} f O →
            (∀ t ∈ A.support,
              f (t.eval O) - f xstar ≤ η + α * (sSup (f '' Ω) - f xstar)) ∧
            expectedQueries A O ≤
              ENNReal.ofReal (C * n * Real.log (2 + (n : ℝ) * (R / w) / α)) := by
  sorry

end QAlgorithms.Papers.LSW15
