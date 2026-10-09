import QAlgorithms.Defs.GradientMethods

/-!
# Nannicini, Chapter 5 (part b): finite-difference subgradients for separation from membership

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §5.1.4: Lemma 5.28 (p.121), Lemma 5.30 (p.122), Lemma 5.32 (p.123).
Proposition 5.31 (p.122) is not stated (see `HARD.md`).

Conventions. A point of `ℝ^d` is `Fin d → ℝ` (coordinate `j` is the source's `j + 1`). The
finite-difference gradient (Def. 5.26) is the frozen `fdGradient`, the finite-difference Laplace
approximation (Def. 5.27) is the frozen `fdLaplacian`, the ℓ1 ball `B_1(x, r)` (Def. 5.20) is the
frozen `ballL1`, and subgradients (Def. 5.24) are the frozen `IsEpsSubgradOn` with `ϵ = 0`, the
domain being the ball on which `f` is given. A function given only on a ball is a total function
on `ℝ^d` whose values outside the ball are never read: the hypotheses (convexity, Lipschitz
continuity, the subgradient inequality) and the finite-difference formulas only involve points of
the ball. The ℓ∞ ball `B_∞(x, r)` (Def. 5.20) is written out as `{y | ∀ i, |x i - y i| ≤ r}`.
-/

namespace QAlgorithms.Nannicini

open MeasureTheory

/-- Nannicini p.121, Lemma 5.28 (Lem. 10 in van Apeldoorn et al. 2020a). Let `η > 0`,
`x ∈ ℝ^d`, and `f : B_1(x, η) → ℝ` convex. Then
`sup_{g ∈ ∂f(x)} ‖g − ∇^(η) f(x)‖_1 ≤ (1/2) η Δ^(η) f(x)`.

The supremum is unfolded: every subgradient `g` of `f` at `x` (Def. 5.24, `g` a linear form,
the subgradient inequality over the domain `B_1(x, η)` of `f`) satisfies the bound; the ℓ1 norm
of `g − ∇^(η) f(x)` is `∑_j |g(e_j) − ∇^(η) f(x)_j|`. -/
theorem fdGradient_near_subgradient {d : ℕ} (η : ℝ) (hη : 0 < η) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ (ballL1 x η) f)
    (g : Module.Dual ℝ (Fin d → ℝ)) (hg : IsEpsSubgradOn (ballL1 x η) f 0 x g) :
    ∑ j : Fin d, |g (Pi.single j 1) - fdGradient η f x j| ≤ 2⁻¹ * η * fdLaplacian η f x := by
  sorry

/-- Nannicini p.122, Lemma 5.30 (Lem. 11 in van Apeldoorn et al. 2020a). Let `0 < η < r`, and
let `f : B_∞(x, r + η) → ℝ` be convex and `L`-Lipschitz. Then
`E_{z ∈ B_∞(x, r)} Δ^(η) f(z) ≤ dL/r`, the expectation over a uniformly random point `z` of the
cube `B_∞(x, r)` (the average with respect to Lebesgue measure on `ℝ^d`).

The Lipschitz condition is with respect to the Euclidean norm (the book's convention for a norm
without subscript, p.11). -/
theorem fdLaplacian_average_le {d : ℕ} (η r L : ℝ) (hη : 0 < η) (hηr : η < r) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ {y | ∀ i, |x i - y i| ≤ r + η} f)
    (hL : ∀ y ∈ {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r + η},
      ∀ y' ∈ {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r + η},
        |f y - f y'| ≤ L * Real.sqrt (∑ i, (y i - y' i) ^ 2)) :
    ⨍ z in {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r}, fdLaplacian η f z ≤ d * L / r := by
  sorry

/-- Nannicini p.123, Lemma 5.32 (Lem. 17 in van Apeldoorn et al. 2020a). Let `η > 0`,
`z ∈ ℝ^d`, and `f : B_1(z, η) → ℝ` convex. Then
`sup_{y ∈ B_1(0, η)} |f(z + y) − f(z) − ⟨∇^(η) f(z), y⟩| ≤ (1/2) η² Δ^(η) f(z)`.

The supremum is unfolded as the bound at every `y ∈ B_1(0, η)`; `⟨·, ·⟩` is the standard inner
product of `ℝ^d`. -/
theorem fdLinearization_deviation_le {d : ℕ} (η : ℝ) (hη : 0 < η) (z : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ (ballL1 z η) f)
    (y : Fin d → ℝ) (hy : y ∈ ballL1 0 η) :
    |f (z + y) - f z - ∑ j, fdGradient η f z j * y j| ≤ 2⁻¹ * η ^ 2 * fdLaplacian η f z := by
  sorry

end QAlgorithms.Nannicini
