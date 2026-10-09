import QAlgorithms.Defs.Information

/-!
# de Wolf, Chapter 15: Quantum encodings, with a non-quantum application

R. de Wolf, *Quantum Computing: Lecture Notes*, §15.2–15.3 (PDF pp.139–144): Nayak's bound on
quantum random access codes (Theorem 4), the Katz–Trevisan normal form for decoders of locally
decodable codes (Fact 1), and the exponential lower bound on 2-query LDCs (Theorem 5).
-/

namespace QAlgorithms.DeWolf

/-- de Wolf p.142, Theorem 4 (Nayak). If `x ↦ ρ_x` encodes `n`-bit strings into `m`-qubit density
matrices so that for every `i` some two-outcome measurement `{M_i, I − M_i}` recovers `x_i` with
success probability at least `p` averaged over a uniform `x` (`IsQRAC ρ p`), where `1/2 < p ≤ 1`
(the random-access-code assumption of p.141), then `m ≥ (1 − H(p)) n` with `H` the binary entropy
in bits. -/
theorem nayak_qrac_lower_bound {n m : ℕ} (ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ)
    (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (hρ : IsQRAC ρ p) :
    (1 - binEntropy2 p) * (n : ℝ) ≤ (m : ℝ) := by
  sorry

/-- de Wolf p.143, Fact 1 (Katz & Trevisan + folklore). There are absolute constants `c₁, c₂ > 0`
such that for every `(q, δ, ε)`-LDC `C : {0,1}^n → {0,1}^N` (with `δ, ε > 0`) and every `i ∈ [n]`
there is a set `M_i` of pairwise disjoint tuples of at most `q` indices of `[N]`, with
`|M_i| ≥ c₁ δ ε N / q²`, and a bit `a_{i,t}` for each `t ∈ M_i`, such that for each `t ∈ M_i`,
`Pr_x[x_i = a_{i,t} ⊕ ⊕_{j ∈ t} C(x)_j] ≥ 1/2 + c₂ ε / 2^q` for uniform `x ∈ {0,1}^n`. -/
theorem ldc_decoder_normalForm :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (n N q : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)),
        0 < δ → 0 < ε → IsLDC q δ ε C →
        ∀ i : Fin n, ∃ M : Finset (Finset (Fin N)),
          (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧
          (∀ t ∈ M, t.card ≤ q) ∧
          c₁ * (δ * ε * (N : ℝ) / (q : ℝ) ^ 2) ≤ (M.card : ℝ) ∧
          ∃ a : Finset (Fin N) → Bool, ∀ t ∈ M,
            1 / 2 + c₂ * (ε / (2 : ℝ) ^ q) ≤
              ((Finset.univ.filter fun x : Fin n → Bool =>
                  x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
                (2 : ℝ) ^ n := by
  sorry

/-- de Wolf p.144, Theorem 5. If `C : {0,1}^n → {0,1}^N` is a `(2, δ, ε)`-locally decodable code,
then `N ≥ 2^{Ω(δ² ε⁴ n)}`: there are constants `c > 0` and `n₀`, uniform over `N, δ, ε, C`, such
that every `(2, δ, ε)`-LDC with `δ, ε > 0` and `n ≥ n₀` has `N ≥ 2^{c δ² ε⁴ n}`. -/
theorem ldc_two_query_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (n N : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)),
        n₀ ≤ n → 0 < δ → 0 < ε → IsLDC 2 δ ε C →
        (2 : ℝ) ^ (c * δ ^ 2 * ε ^ 4 * (n : ℝ)) ≤ (N : ℝ) := by
  sorry

end QAlgorithms.DeWolf
