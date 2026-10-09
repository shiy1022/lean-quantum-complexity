import QAlgorithms.Defs.Fourier

/-!
# Childs, Chapter 5: Discrete log and the hidden subgroup problem

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 5 (PDF pp. 29–32).
-/

namespace QAlgorithms.Childs

universe u v

/-- **Childs, Theorem 5.1** (PDF p. 30, proof pp. 30–31). Suppose that `G` has a set `ℋ` of `N`
subgroups whose only common element is the identity. Then to solve the hidden subgroup problem,
a deterministic classical computer must make `Ω(√N)` queries.

The HSP (§5.3, p. 30): a black-box `f : G → S`, `S` a finite set, is promised to hide some
subgroup `H ≤ G`, i.e. `f x = f y ↔ x⁻¹ * y ∈ H` (`Hides`, eq. (5.1)); the goal is to learn `H`.
A deterministic classical algorithm is a decision tree that queries group elements adaptively,
receives values in `S`, and outputs a subgroup of `G` (outputting `H` itself rather than a
generating set; equivalent for counting queries). "Solves the HSP" means: for every subgroup
`H ≤ G` and every `f` hiding `H`, the output is `H`. The query count on input `f` is the number
of queries along the path `f` follows.

Conventions made explicit: `G` is finite, and `|S| ≥ |G|`, so that every subgroup of `G` can be
hidden (the proof's adversary answers each new query with a fresh label; with a small `S`, e.g.
`|S| = 1`, only `H = G` can be hidden and zero queries suffice). `Ω` is read with a threshold
`N₀`, and the constants `c`, `N₀` are absolute: they precede the group, the set `S`, the family
and the algorithm. The lower bound is "every correct algorithm has a hard input".

"Whose only common element is the identity" is read as in the section's lead-in ("a large
number of *trivially intersecting* subgroups") and as the proof uses it: any two distinct members
of `ℋ` meet only in the identity. The proof counts the at most `t(t − 1)` non-identity values
`g_j⁻¹ g_k` against the `N` members of `ℋ`, and that count needs each such value to lie in at most
one member. Read instead as `⋂ ℋ = {1}`, the theorem is false: in the cyclic group of squarefree
order `p₁ ⋯ p_k`, all `2^k` subgroups intersect in `{1}`, yet querying `1` and one element of
each prime order `p_i` (`k + 1` queries) determines `H`. -/
theorem hsp_classical_deterministic_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (G : Type u) [Group G] [Fintype G] (S : Type v) [Fintype S],
        Fintype.card G ≤ Fintype.card S →
        ∀ ℋ : Finset (Subgroup G), ℋ.card = N →
        (ℋ : Set (Subgroup G)).Pairwise (fun H K => H ⊓ K = ⊥) →
        ∀ A : DecisionTree G S (Subgroup G),
          (∀ (H : Subgroup G) (f : G → S), Hides f H → A.eval f = H) →
          ∃ (H : Subgroup G) (f : G → S), Hides f H ∧
            c * Real.sqrt (N : ℝ) ≤ (A.queries f : ℝ) := by
  sorry

end QAlgorithms.Childs
