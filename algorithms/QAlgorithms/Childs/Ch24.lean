import QAlgorithms.Defs.Adversary

/-!
# Childs, Chapter 24: span programs and formula evaluation

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 24 (PDF pp. 123–128).

Inputs are bit strings over a finite index type `ι` (the source's `[n]`); a possibly partial
Boolean function is `f` together with its domain `D` (the source's `S ⊆ {0,1}^n`). `advPm f D`
is the source's `Adv±(f)` (24.1), valued in `ℝ≥0∞` and equal to `0` when `f` is constant on `D`.
-/

namespace QAlgorithms.Childs

open scoped NNReal ENNReal

/-- Childs, Theorem 24.1 (PDF p. 124): the dual of the general adversary bound. For any
`f : S → {0,1}` with `S ⊆ {0,1}^n`, `Adv±(f) = min max{C₀, C₁}`, the minimum over all positive
integers `d` and all families of vectors `|v_{x,i}⟩ ∈ ℂ^d` (`x ∈ S`, `i ∈ [n]`) satisfying
(24.3): `∑_{i : x_i ≠ y_i} ⟨v_{x,i}|v_{y,i}⟩ = 1 − δ_{f(x),f(y)}` for all `x ≠ y`, where
`C_b = max_{x ∈ f⁻¹(b)} ∑_i ‖|v_{x,i}⟩‖²`. "Min" is rendered as `IsLeast`: the value is attained
by a feasible family and is a lower bound on every feasible objective. -/
theorem adversary_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool)
    (D : Finset (ι → Bool)) :
    IsLeast {r : ℝ≥0∞ | ∃ (d : ℕ) (v : D → ι → EuclideanSpace ℂ (Fin d)), 0 < d ∧
        DualFeasibleChilds f D d v ∧ r = (childsDualObjective f D v : ℝ≥0∞)}
      (advPm f D) := by
  sorry

/-- Childs, Theorem 24.2 (PDF p. 126): for total `f : {0,1}^n → {0,1}` and
`g : {0,1}^m → {0,1}`, `Adv±(f ∘ g) ≤ Adv±(f) Adv±(g)`, where
`(f ∘ g)(y) = f(g(y¹), …, g(yⁿ))` with `yⁱ ∈ {0,1}^m` the `i`-th block of `y`. The composed input
is indexed by `ι × κ`, `y (i, j)` being bit `j` of block `i`. -/
theorem adversary_compose_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool) :
    advPm (blockCompose f g) Finset.univ ≤ advPm f Finset.univ * advPm g Finset.univ := by
  sorry

/-- Childs, Lemma 24.3 (PDF p. 128), the effective spectral gap lemma. Let `Π` and `∆` be the
orthogonal projections onto subspaces `K` and `L` of a finite-dimensional complex inner product
space, `U = (2Π − I)(2∆ − I)`, `ω ≥ 0`, and `P_ω` the projector onto the span of the eigenvectors
of `U` with eigenvalues `e^{iθ}`, `|θ| < ω`. If `|ϕ⟩` is a unit vector with `∆|ϕ⟩ = 0`, then
`‖P_ω Π|ϕ⟩‖ ≤ ω/2`. -/
theorem effective_spectral_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (K L : Submodule ℂ E) (ω : ℝ) (hω : 0 ≤ ω) (ϕ : E)
    (hϕ : ‖ϕ‖ = 1) (hΔ : L.starProjection ϕ = 0) :
    ‖eigenProjection (reflProduct K L)
        {μ : ℂ | ∃ θ : ℝ, |θ| < ω ∧ μ = Complex.exp (θ * Complex.I)}
        (K.starProjection ϕ)‖ ≤ ω / 2 := by
  sorry

end QAlgorithms.Childs
