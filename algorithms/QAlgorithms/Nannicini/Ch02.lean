import QAlgorithms.Defs.Basic

/-!
# Nannicini, Chapter 2 (§2.3.3): Simon's algorithm, full description and analysis

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages). Vectors of `𝔽₂ⁿ` (Rem. 2.7) are `Fin n → ZMod 2`; the inner product modulo 2 of
Def. 1.34 is the dot product `k ⬝ᵥ a` computed in `ZMod 2`.
-/

namespace QAlgorithms.Nannicini

open QAlgorithms

open Classical in
/-- Nannicini p.51, Proposition 2.8: let `a ∈ 𝔽₂ⁿ` be nonzero, so that the vectors orthogonal to
`a` (`k ⬝ᵥ a = 0` in `𝔽₂`) form a subspace `V_a` of dimension `n − 1`. If `k⁽¹⁾, …, k⁽ⁿ⁺ᵗ⁾` are
drawn independently and uniformly at random from `V_a`, then the probability that among them
there are `n − 1` linearly independent vectors (over `𝔽₂`) is at least `1 − 1/2^{t+1}`.

The probability is the fraction of the `|V_a|^{n+t}` equally likely tuples `k : Fin (n+t) → V_a`
for which some `n − 1` distinct indices carry linearly independent vectors. -/
theorem simon_linearIndependent_prob (n t : ℕ) (a : Fin n → ZMod 2) (ha : a ≠ 0) :
    (Fintype.card {k : Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0} //
        ∃ s : Fin (n - 1) ↪ Fin (n + t),
          LinearIndependent (ZMod 2) (fun i => ((k (s i) : {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) :
            Fin n → ZMod 2))} : ℝ) /
      (Fintype.card (Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) : ℝ) ≥
      1 - 1 / 2 ^ (t + 1) := by sorry

end QAlgorithms.Nannicini
