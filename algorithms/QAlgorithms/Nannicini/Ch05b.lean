import QAlgorithms.Defs.GradientMethods

/-!
# Nannicini, Chapter 5 (part b): finite-difference subgradients for separation from membership

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §5.1.4: Lemma 5.28 (p.121), Lemma 5.30 (p.122), Lemma 5.32 (p.123).
Proposition 5.31 (p.122) is stated as a corrected theorem (see its docstring).

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

/-- Corrected statement. Nannicini p.122, Proposition 5.31 (Lem. 12 in van Apeldoorn et al.
2020a). Printed: let `r > 0`, `L > 0`, `0 < δ < 1/3`, `0 < ϵ < rL√d/δ`, `f : ℝ^d → ℝ` convex and
`L`-Lipschitz on `B_∞(0, 2r)`, `f̃` with `|f(x) − f̃(x)| ≤ ϵ` on `B_∞(0, 2r)`; then for a uniformly
random `z ∈ B_∞(0, r)` "we can compute parameters `0 < η < r`, `ϵ′ > ϵ`" such that with probability
at least `1 − δ`, `∇^(η) f(z) ∈ ∂_ϵ′ f(0)`.

Changes, and why the printed version cannot be stated as is:
1. The finite differences are taken of `f̃`, not `f`: as printed `f̃` plays no role, while the text
   just before (p.122) says the finite-difference approximation uses the estimate of the function,
   not its exact value.
2. The `ϵ′`-subgradient inequality (Def. 5.24) is required on `B_∞(0, 2r)`, the set on which the
   hypotheses control `f` and `f̃`, not on all of `ℝ^d`. Over `ℝ^d` the claim is false: for linear
   `f` and a perturbation `f̃`, `∇^(η) f̃(z) = ∇f + e` with `e ≠ 0`, and `⟨e, x⟩` is unbounded.
3. `η` and `ϵ′` are never given (the proof omits the "cumbersome expressions"). The statement holds
   for every `η ∈ (0, r)` (the source's only condition on `η`), with the explicit
   `ϵ′ = 2Lr√d + ηdL/δ + 2rdϵ/η`, assembled from the proof sketch's steps: Lemma 5.28 and 5.30
   (gradient error `ηdL/(2r)` in expectation), Markov's inequality (error `≤ ηdL/(2rδ)` with
   probability `1 − δ`), the `f̃` error `dϵ/η` in ℓ1, and "z and 0 are close and f is
   L-Lipschitz" (the term `2Lr√d`). This constant is the drafter's instantiation of the sketch.
4. "With probability at least `1 − δ`" for a uniformly random `z` is stated as a measurable
   `S ⊆ B_∞(0, r)` of Lebesgue measure at least `(1 − δ) vol(B_∞(0, r))` on which the conclusion
   holds (since `f̃` is arbitrary, the event itself need not be measurable).

The Lipschitz condition uses the Euclidean norm (the book's convention, p.11). -/
theorem fdGradient_random_point_epsSubgrad {d : ℕ} (r L ϵ δ : ℝ) (hr : 0 < r) (hL : 0 < L)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 3) (hϵ0 : 0 < ϵ) (hϵ : ϵ < r * L * Real.sqrt d / δ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hLip : ∀ y ∈ {y : Fin d → ℝ | ∀ i, |y i| ≤ 2 * r},
      ∀ y' ∈ {y : Fin d → ℝ | ∀ i, |y i| ≤ 2 * r},
        |f y - f y'| ≤ L * Real.sqrt (∑ i, (y i - y' i) ^ 2))
    (ft : (Fin d → ℝ) → ℝ) (hft : ∀ x ∈ {x : Fin d → ℝ | ∀ i, |x i| ≤ 2 * r}, |f x - ft x| ≤ ϵ)
    (η : ℝ) (hη0 : 0 < η) (hηr : η < r) :
    ϵ < 2 * L * r * Real.sqrt d + η * d * L / δ + 2 * r * d * ϵ / η ∧
    ∃ S ⊆ {z : Fin d → ℝ | ∀ i, |z i| ≤ r}, MeasurableSet S ∧
      (1 - δ) * volume.real {z : Fin d → ℝ | ∀ i, |z i| ≤ r} ≤ volume.real S ∧
      ∀ z ∈ S, IsEpsSubgradOn {x : Fin d → ℝ | ∀ i, |x i| ≤ 2 * r} f
        (2 * L * r * Real.sqrt d + η * d * L / δ + 2 * r * d * ϵ / η) 0
        (∑ j : Fin d, fdGradient η ft z j • (LinearMap.proj j : (Fin d → ℝ) →ₗ[ℝ] ℝ)) := by
  sorry

end QAlgorithms.Nannicini
