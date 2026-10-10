import QAlgorithms.Defs.ConvexOpt

/-!
# Bansal, Gupta: Potential-function proofs for gradient methods

N. Bansal, A. Gupta, *Potential-function proofs for gradient methods* (arXiv:1712.04581v3),
cited "Bansal–Gupta p.N" (PDF pages), §4.1.

Objects (frozen definition layer): the Bregman divergence `D_h(y ‖ x)` (p.17) is
`bregmanDiv h y x`; the Bregman projection `Π^h_K(x')` (p.18) is characterized by
`IsBregmanProjection h K x' b`; `α`-strong convexity of `h` with respect to the norm `‖·‖` (p.16)
is `IsStronglyConvexWrt h α`; a run of mirror descent with constant step size `η` (4.37) is
`IsMirrorDescentRun h K η f x0 T x`. The space `E` carries an arbitrary norm; gradients are
Fréchet derivatives `E →L[ℝ] ℝ`, whose operator norm is the dual norm (4.35).
-/

namespace QAlgorithms.Papers.BansalGupta19

/-- Bansal–Gupta p.18, Theorem 4.2 (cited by Nannicini, Theorem 8.5): the mirror descent regret
bound. Let `K` be a convex body, `f_1, …, f_T` convex functions, `‖·‖` a norm and `h` an
`α_h`-strongly convex function with respect to `‖·‖`. Mirror descent started at `x0` with
constant step size `η` produces `x_1, …, x_T` such that for all `x* ∈ K`
`Σ_{t=1}^T f_t(x_t) − Σ_{t=1}^T f_t(x*) ≤ D_h(x* ‖ x0)/η + η Σ_{t=1}^T ‖∇f_t(x_t)‖_*² / (2α_h)`
(4.40).

Formalization choices.
* The second sum is printed `Σ_{t=1}^n f_t(x*)`; `n` is a typo for `T` (the proof sums the
  amortized inequality over the same `t`), corrected here (trap 30).
* "Convex body" is the p.2 standing assumption: closed, convex, nonempty interior. Convex
  functions are differentiable on the whole space and convex over `K` (p.2); `h : E → ℝ` (p.17).
* `E` is finite-dimensional (the paper's `ℝ^d`).
* The run: `x_1 = Π^h_K(x0)` and, for `1 ≤ t < T`, `x_{t+1} = Π^h_K(x'_{t+1})` with
  `∇h(x'_{t+1}) = ∇h(x_t) − η ∇f_t(x_t)` (4.37); every run satisfying this is covered.
* `α_h > 0` and `η > 0` are the field's implicit conventions (the bound divides by both). -/
theorem mirrorDescent_regret {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKint : (interior K).Nonempty) (T : ℕ) (f : ℕ → E → ℝ)
    (hfdiff : ∀ t ∈ Finset.Icc 1 T, Differentiable ℝ (f t))
    (hfconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ K (f t)) (h : E → ℝ) (αh : ℝ) (hαh : 0 < αh)
    (hh : IsStronglyConvexWrt h αh) (η : ℝ) (hη : 0 < η) (x0 : E) (x : ℕ → E)
    (hx : IsMirrorDescentRun h K η f x0 T x) (xstar : E) (hxstar : xstar ∈ K) :
    ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t xstar ≤
      bregmanDiv h xstar x0 / η +
        η * (∑ t ∈ Finset.Icc 1 T, ‖fderiv ℝ (f t) (x t)‖ ^ 2) / (2 * αh) := by
  sorry

end QAlgorithms.Papers.BansalGupta19
