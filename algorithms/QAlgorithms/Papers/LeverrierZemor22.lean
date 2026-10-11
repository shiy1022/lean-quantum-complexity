import QAlgorithms.Defs.LeftRightComplex

/-!
# A. Leverrier, G. Zémor, *Quantum Tanner codes* (arXiv:2202.13641v3)

Cited "LZ p.N" (PDF pages). The left-right Cayley complex (§3.2, p.11–12; §4.1, p.17) of a finite
group `G` and self-inverse sets `A = A⁻¹`, `B = B⁻¹` with `|A| = |B| = Δ` has vertices
`V₀ = G × {0}` (`G × {false}`), `V₁ = G × {1}` (`G × {true}`) and squares
`{(g,0), (ag,1), (gb,1), (agb,0)}` (frozen `lzSquare`, `lzSquares`). The local view of
`x ∈ F₂^Q` at `v`, read as an `A × B` array through `φ_v` (p.17), is the frozen `lzLocalView`;
the Tanner code `C₁ = T(G₁^◻, C₁^⊥) = {x : x_v ∈ C_A ⊗ F₂^B + F₂^A ⊗ C_B for all v ∈ V₁}`
(eq. (4), p.18) is `lzTannerCode1`. The word of `F₂^Q` supported on `Q(v)` and equal there (through
`φ_v`) to a local array `c` is `lzExtend v c`.

The double covers `G_A`, `G_B` of `Cay(G, A)`, `Cay(G, B)` (p.12) have adjacency matrices
`bipartiteDoubleCover (leftCayleyAdj A)` and `bipartiteDoubleCover (rightCayleyAdj B)`;
"Ramanujan" is the §3.1 definition (connected, every eigenvalue other than `±Δ` of absolute value
`≤ 2√(Δ−1)`), frozen `IsRamanujanAdj`.
-/

namespace QAlgorithms.Papers.LeverrierZemor22

open QAlgorithms

universe u

/-- LZ Theorem 1 (p.8, restated and proved p.19; Definitions 5 and 8, pp.15–16; standing
assumptions of §3.2 and §4.1, pp.11–12, 17).

Fix `ε ∈ (0, 1/2)`, `γ ∈ (1/2 + ε, 1)` and `δ > 0`. There is `Δ₀` (depending only on `ε, γ, δ`)
such that for every `Δ ≥ Δ₀`, every left-right Cayley complex over a finite group `G` with
self-inverse `A, B ⊆ G`, `|A| = |B| = Δ`, satisfying TNC (eq. (1)) and whose double covers
`G_A`, `G_B` are Ramanujan, and all component codes `C_A ⊆ F₂^A`, `C_B ⊆ F₂^B` with minimum distance
`≥ δΔ` whose dual tensor code `C_A ⊗ F₂^B + F₂^A ⊗ C_B` is `w`-robust with `p`-resistance to
puncturing for `w = Δ^{3/2 − ε/2}`, `p = Δ^γ`: every `x ∈ C₁` with `0 < |x| < δn/(4Δ^{3/2+ε})`,
`n = |Q|`, admits a vertex `v ∈ V₀` and a tensor codeword `c ∈ C_A ⊗ C_B` such that the word `y`
supported on `Q(v)` and equal there to `c` lies in `C₁` and `|x + y| < |x|`.

The source's "there exists an infinite family of square complexes `X`" is stated for every
complex satisfying the hypotheses the proof uses (p.19, first sentence); the family itself is
the cited construction of [DEL+21]. -/
theorem quantumTanner_weight_reduction :
    ∀ ε γ δ : ℝ, 0 < ε → ε < 1 / 2 → 1 / 2 + ε < γ → γ < 1 → 0 < δ →
      ∃ Δ0 : ℕ, ∀ Δ : ℕ, Δ0 ≤ Δ →
        ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (A B : Finset G),
          (∀ a ∈ A, a⁻¹ ∈ A) → (∀ b ∈ B, b⁻¹ ∈ B) → A.card = Δ → B.card = Δ →
          IsTNC A B →
          IsRamanujanAdj (bipartiteDoubleCover (leftCayleyAdj A)) Δ →
          IsRamanujanAdj (bipartiteDoubleCover (rightCayleyAdj B)) Δ →
          ∀ (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)),
            HasMinDistAtLeast CA (δ * Δ) → HasMinDistAtLeast CB (δ * Δ) →
            IsRobustResistant CA CB ((Δ : ℝ) ^ ((3 : ℝ) / 2 - ε / 2)) ((Δ : ℝ) ^ γ) →
            ∀ x ∈ lzTannerCode1 A B CA CB, 0 < hammingNorm x →
              (hammingNorm x : ℝ) <
                δ * ((lzSquares A B).card : ℝ) / (4 * (Δ : ℝ) ^ ((3 : ℝ) / 2 + ε)) →
              ∃ g : G, ∃ c ∈ tensorCode CA CB,
                lzExtend (g, false) c ∈ lzTannerCode1 A B CA CB ∧
                  hammingNorm (x + lzExtend (g, false) c) < hammingNorm x := by
  sorry

end QAlgorithms.Papers.LeverrierZemor22
