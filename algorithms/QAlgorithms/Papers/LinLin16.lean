import QAlgorithms.Defs.AdaptiveQuery

/-!
# Lin–Lin, *Upper bounds on quantum query complexity inspired by the Elitzur–Vaidman bomb tester*

C. Y.-Y. Lin, H.-H. Lin, arXiv:1410.0932v2, cited "LinLin p.N" (PDF pages).

Model (§2.2, p.4–5): the input is a Boolean string `x ∈ {0,1}^N` (`x i = true` iff element `i` is
marked); the oracle is the XOR oracle `|i, b⟩ ↦ |i, b ⊕ x_i⟩` (frozen `xorOracle`; the paper
writes the record register first, the order of tensor factors is immaterial); algorithms
interleave input-independent unitaries with oracle calls (frozen `QueryAlg`), and may measure
and continue adaptively (frozen `AdaptiveQueryAlg`, fixed before the input). Elements are
0-indexed: the source's `d`-th element is index `d - 1`.
-/

namespace QAlgorithms.Papers.LinLin16

/-- **Theorem 10** (LinLin p.13; restated and proved in Appendix C, p.31–32): finding the first
marked element in a list. There is an absolute constant `C > 0` such that for every list length
`N` there is a quantum query algorithm (fixed before the input, built from input-independent
unitaries and the XOR oracle) which, for every input `x : Fin N → Bool`,

* outputs the first marked element (`some i`) or "no marked element" (`none`), correctly with
  probability at least `9/10` (bounded error; the proof's total error is `δ < 1/10`);
* if the first marked element is the `d`-th element (index `i = d - 1`), uses an expected number
  of queries at most `C √d`;
* if there are no marked elements, uses at most `C √N` queries on every run and always outputs
  `none`.

The "time" bounds of the source are not formalized (the paper fixes no time model). -/
theorem firstMarked_search :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ A : AdaptiveQueryAlg (Fin N) (Option (Fin N)),
      ∀ x : Fin N → Bool,
        A.outProb x (firstMarked x) ≥ 9 / 10 ∧
        (∀ i : Fin N, firstMarked x = some i →
          A.expQueries x ≤ C * Real.sqrt ((i : ℝ) + 1)) ∧
        (firstMarked x = none →
          A.outProb x none = 1 ∧ (A.maxQueries x : ℝ) ≤ C * Real.sqrt N) := by
  sorry

end QAlgorithms.Papers.LinLin16
