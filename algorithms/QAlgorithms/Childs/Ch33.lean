import QAlgorithms.Defs.Hamiltonian

/-!
# Childs, Chapter 33: universality of adiabatic quantum computation

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 33 (PDF pp. 179–184).

Within the `(k + 1)`-dimensional computational subspace spanned by `|ψ_0⟩, …, |ψ_k⟩` (33.3),
the interpolated Hamiltonian `H(s) = (1 − s) H_B + s H_C` (33.13) acts, by (33.14)–(33.15), as
the real symmetric matrix (33.16), which is `clockPathMatrix k s`: entry `(0,0)` is `s − 1`,
the first off-diagonals are `−s`, all other entries `0`. `spectralGap` is the second smallest
minus the smallest eigenvalue, counted with multiplicity.
-/

namespace QAlgorithms.Childs

/-- Childs, Lemma 33.1 (PDF p. 182; matrix (33.16) on PDF p. 181): the gap between the smallest
and second smallest eigenvalues of the matrix (33.16) for `s ∈ [0, 1]` is `Ω(1/k²)`. The
constant `c > 0` and the threshold `k₀` are chosen before `k` and are uniform over
`s ∈ [0, 1]`. -/
theorem clockPathMatrix_gap :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c / (k : ℝ) ^ 2 ≤ spectralGap (clockPathMatrix k s) := by
  sorry

end QAlgorithms.Childs
