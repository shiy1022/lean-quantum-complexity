import QAlgorithms.Defs.Walk

/-!
# Childs, Chapter 27: simulating Hamiltonian dynamics

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 27 (PDF pp. 141–145).

Only Lemma 27.1 (§27.4, p. 143) is stated: the local `d²`-edge-colouring of a bipartite graph of
maximum degree `d`. Graphs are `SimpleGraph (Fin N)` (the source numbers the vertices
`1, …, N`); the bipartition is given as a side map (`IsBipartition`), and neighbour access is a
duplicate-free list of the neighbours of each vertex (`IsNeighbourList`), as in the proof's
`idx(α, β)`, "the index of vertex `β` in the list of neighbors of `α`".
-/

namespace QAlgorithms.Childs

/-- Childs, Lemma 27.1 (PDF p. 143). "Suppose we are given an undirected, bipartite graph `G`
with `N` vertices and maximum degree `d`, and that we can efficiently compute the neighbors of
any given vertex. Then there is an efficiently computable edge coloring of `G` with at most `d²`
colors."

Formal reading: for every `N` and `d` there is one colouring rule `rule`, fixed before the graph,
whose value on an edge `{α, β}` depends only on the two endpoints, their sides of the
bipartition and their neighbour lists (two neighbour-list queries). For every bipartite graph `G`
on `Fin N` with a given bipartition `side` and maximum degree at most `d`, and every enumeration
`nbr` of the neighbours of each vertex, the map `{α, β} ↦ rule (α, side α, nbr α) (β, side β,
nbr β)` is a proper edge colouring of `G` (symmetric on edges, distinct colours on distinct edges
at a common vertex) that uses at most `d²` distinct colours on the edges of `G`.

Not formalized: the running time of `rule` ("efficiently computable"); the source gives no
machine model. Graph-independence and locality of `rule` are the formal content kept. Colours
live in `ℕ × ℕ` rather than `Fin d × Fin d` so that the rule is total at `d = 0`; the bound
`≤ d²` is on the set of colours actually used on edges. -/
theorem bipartite_local_edgeColouring (N d : ℕ) :
    ∃ rule : Fin N × Bool × List (Fin N) → Fin N × Bool × List (Fin N) → ℕ × ℕ,
      ∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (side : Fin N → Bool),
        IsBipartition G side → G.maxDegree ≤ d →
        ∀ nbr : Fin N → List (Fin N), IsNeighbourList G nbr →
          IsProperEdgeColouring G (fun u v => rule (u, side u, nbr u) (v, side v, nbr v)) ∧
          ((Finset.univ.filter fun p : Fin N × Fin N => G.Adj p.1 p.2).image
              fun p => rule (p.1, side p.1, nbr p.1) (p.2, side p.2, nbr p.2)).card ≤ d ^ 2 := by
  sorry

end QAlgorithms.Childs
