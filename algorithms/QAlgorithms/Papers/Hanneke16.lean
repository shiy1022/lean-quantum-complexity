import QAlgorithms.Defs.PACSampleComplexity

/-!
# Hanneke: The optimal sample complexity of PAC learning

S. Hanneke, *The optimal sample complexity of PAC learning* (arXiv:1507.00473v4), cited
"Hanneke p.N" (PDF pages).

Notation of §2 (pp.1–3), in the frozen layer `QAlgorithms.Defs.PACSampleComplexity`:
the instance space `X` is a nonempty measurable space, the label space `Y = {−1, +1}` is `Bool`,
a classifier is a measurable `h : X → Bool`, the concept space `C` is a set of classifiers with
`|C| ≥ 3`; `er_P(h; f⋆) = P(x : h(x) ≠ f⋆(x))` is `errRate P h f⋆`; the VC dimension `d` is
`vcDimSet C`; the sample complexity `M(ε, δ)` of Definition 1 (p.2), with randomized algorithms
(footnote 2: internal randomness on a probability space independent of the data), is
`pacSampleComplexity C ε δ : ℕ∞` (`⊤` when no sample size works); `Log(z) = ln(max{z, e})`
(p.3) is `logE`.
-/

namespace QAlgorithms.Papers.Hanneke16

open QAlgorithms.Learning

universe u

/-- Hanneke p.7, Theorem 2 and Corollary 3: `M(ε, δ) = Θ((1/ε)(d + Log(1/δ)))`.

The `O`/`Ω` notation is the paper's (p.3): there are numerical constants `ε₀, δ₀ ∈ (0, 1)` and
`c₀ ∈ (0, ∞)`, "independent of `C` and `X`" (so `c₀` cannot depend on `d`), such that the bound
holds for all `ε ∈ (0, ε₀)`, `δ ∈ (0, δ₀)`. The constants are therefore quantified before the
instance space and the concept class.

1. (Theorem 2, the `O` half) `M(ε, δ)` is finite and `M(ε, δ) ≤ c₀ (d + Log(1/δ)) / ε`.
2. (the `Ω` half, bound (1) p.3) `(d + Log(1/δ)) / ε ≤ c₁ M(ε, δ)`, read as trivially true
   when `M(ε, δ) = ∞`.

Standing assumptions (pp.1–3): `X` nonempty with a σ-algebra; every `h ∈ C` measurable;
`|C| ≥ 3`; `d < ∞` (p.3, "for the remainder of this article we suppose d < ∞"); and p.3: "we
adopt the assumption that the events appearing in probability claims below are indeed
measurable. For our purposes, this comes into effect only in the application of classic
generalization bounds for sample-consistent classifiers (Lemma 4 below)." That assumption is
`ConsistentEventsMeasurable C`: the events of Lemma 4 (some `h ∈ C` consistent with the sample
has error above a threshold) are measurable for every `P`, `f⋆ ∈ C`, `m`. -/
theorem sampleComplexity_theta :
    (∃ ε0 δ0 c0 : ℝ, 0 < ε0 ∧ ε0 < 1 ∧ 0 < δ0 ∧ δ0 < 1 ∧ 0 < c0 ∧
      ∀ (X : Type u) [MeasurableSpace X] [Nonempty X] (C : Set (X → Bool)) (d : ℕ),
        (∀ c ∈ C, Measurable c) → 3 ≤ C.encard → vcDimSet C = (d : ℕ∞) →
        ConsistentEventsMeasurable C →
        ∀ ε δ : ℝ, 0 < ε → ε < ε0 → 0 < δ → δ < δ0 →
          ∃ m : ℕ, pacSampleComplexity C ε δ = (m : ℕ∞) ∧
            (m : ℝ) ≤ c0 * (((d : ℝ) + logE (1 / δ)) / ε)) ∧
    (∃ ε1 δ1 c1 : ℝ, 0 < ε1 ∧ ε1 < 1 ∧ 0 < δ1 ∧ δ1 < 1 ∧ 0 < c1 ∧
      ∀ (X : Type u) [MeasurableSpace X] [Nonempty X] (C : Set (X → Bool)) (d : ℕ),
        (∀ c ∈ C, Measurable c) → 3 ≤ C.encard → vcDimSet C = (d : ℕ∞) →
        ConsistentEventsMeasurable C →
        ∀ ε δ : ℝ, 0 < ε → ε < ε1 → 0 < δ → δ < δ1 →
          ∀ m : ℕ, pacSampleComplexity C ε δ = (m : ℕ∞) →
            ((d : ℝ) + logE (1 / δ)) / ε ≤ c1 * (m : ℝ)) := by
  sorry

end QAlgorithms.Papers.Hanneke16
