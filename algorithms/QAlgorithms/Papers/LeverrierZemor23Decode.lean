import QAlgorithms.Defs.TannerDecoder

/-!
# Decoding quantum Tanner codes (Leverrier–Zémor, arXiv:2208.05537v3)

A. Leverrier, G. Zémor, *Efficient decoding up to a constant fraction of the code length for
asymptotically good quantum codes* / *Decoding quantum Tanner codes* (arXiv:2208.05537v3), cited
"LZ-dec p.N" (PDF pages). The square complex, the codes `C₀`, `C₁`, the stabilizer `C₀^⊥`, the
preprocessing (minimum-weight local corrections `ε_v`, mismatch `Z`), the sequential mismatch
decomposition (Algorithm 2, as a step relation) and the postprocessing are the frozen objects of
`QAlgorithms.Defs.TannerDecoder` and `QAlgorithms.Defs.TensorCode`.
-/

namespace QAlgorithms.Papers.LeverrierZemor23Decode

open QAlgorithms

/-- LZ-dec Theorem 13 (p.20), with the iteration bound of its proof (p.24–25: Lemma 17,
`|Z| ≤ 4|e|`, and `(1 − ε)(|x₁| + ⋯ + |x_m|) ≤ |Z|`).

Fix `ε ∈ (0, 1)` and the constants `δ, κ > 0`. For every large enough constant `Δ` (standing
assumption p.4, p.11: "For a constant `∆` large enough"; `Δ₀` depends on `ε, δ, κ` only), for every
finite group `G` with self-inverse generating sets `A, B`, `|A| = |B| = Δ`, whose left Cayley graph
`Cay(G, A)` and right Cayley graph `Cay(G, B)` are non-bipartite Ramanujan (p.7, p.10), and local
codes `C_A ⊆ F₂^A`, `C_B ⊆ F₂^B` with `dim C_A + dim C_B = Δ` (p.11), all four of `C_A, C_B, C_A^⊥,
C_B^⊥` of distance `≥ δΔ` (p.4), and both dual tensor codes `C_A ⊗ F₂^B + F₂^A ⊗ C_B`,
`C_A^⊥ ⊗ F₂^B + F₂^A ⊗ C_B^⊥` `κ`-product-expanding (p.12): for every σx-type error
`e ∈ F₂^Q` with `|e| < 2^{-11} min(ε³/16, κ)(1 − ε) δ² κ² n / Δ` (`n = |Q| = |G| Δ²`), for every
choice of minimum-weight local corrections `ε_v` (`v ∈ V₁`, Algorithm 1 lines 2–4), and for every
run of the sequential decoder (Algorithm 2, all nondeterministic choices) from the mismatch
`Z = Σ_{v ∈ V₁} ε_v`:
1. the run has made at most `4|e| / (1 − ε)` iterations (linear in `n`);
2. if the current mismatch is nonzero, an iteration is available (the decoder never fails);
3. if the current mismatch is zero, the output `ê = Σ_{v ∈ V₁₀} ε_v + Ĉ₀ + R̂₁` satisfies
   `e + ê ∈ C₀^⊥` (the span of the σx-generators: a valid correction). -/
theorem sequentialDecoder_valid :
    ∀ ε δ κ : ℝ, 0 < ε → ε < 1 → 0 < δ → 0 < κ →
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (A B : Finset G),
      A.card = Δ → B.card = Δ →
      (∀ a ∈ A, a⁻¹ ∈ A) → (∀ b ∈ B, b⁻¹ ∈ B) →
      IsRamanujanAdj (leftCayleyAdj A) Δ →
      (∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ)) →
      IsRamanujanAdj (rightCayleyAdj B) Δ →
      (∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ)) →
      ∀ (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)),
      Module.finrank (ZMod 2) CA + Module.finrank (ZMod 2) CB = Δ →
      HasMinDistAtLeast CA (δ * Δ) → HasMinDistAtLeast CB (δ * Δ) →
      HasMinDistAtLeast (codeDual CA) (δ * Δ) → HasMinDistAtLeast (codeDual CB) (δ * Δ) →
      IsProductExpanding CA CB Δ κ → IsProductExpanding (codeDual CA) (codeDual CB) Δ κ →
      ∀ e : G × A × B → ZMod 2,
      (hammingNorm e : ℝ) < 1 / 2 ^ 11 * min (ε ^ 3 / 16) κ * (1 - ε) * δ ^ 2 * κ ^ 2 *
          (Fintype.card (G × A × B) : ℝ) / Δ →
      ∀ εsel : G × (Bool × Bool) → A × B → ZMod 2,
      (∀ v : G × (Bool × Bool), v.2.1 ≠ v.2.2 → IsMinLocalCorrection CA CB e v (εsel v)) →
      ∀ (s : ℕ → SeqDecState (G × A × B)) (m : ℕ),
        IsSeqDecRun CA CB ε (qtMismatch εsel) s m →
        (1 - ε) * (m : ℝ) ≤ 4 * (hammingNorm e : ℝ) ∧
        ((s m).Z ≠ 0 → ∃ s', SeqDecStep CA CB ε (s m) s') ∧
        ((s m).Z = 0 → e + seqDecOutput εsel (s m) ∈ qtSigmaXSpan CA CB) := by sorry

end QAlgorithms.Papers.LeverrierZemor23Decode
