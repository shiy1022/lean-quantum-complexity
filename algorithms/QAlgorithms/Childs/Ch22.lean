import QAlgorithms.Defs.Polynomial

/-!
# Childs, Chapter 22: The collision problem

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 22 (PDF pp. 111–115).
-/

namespace QAlgorithms.Childs

/-- **Childs, Lemma 22.1** (Kutin; PDF p. 113, with the setting of §22.1, p. 111, (22.3), p. 112,
and §22.5, (22.6)–(22.7), p. 113). Let `p({δ_ij})` be a polynomial in the variables `δ_ij`,
`i, j ∈ {1, …, n}`. For a valid triple `(m, a, b)` (`m ∈ {0, …, n}`, `a ∣ m`, `b ∣ n − m`, with
`a, b ≥ 1` since they are the multiplicities of the `a`-to-one and `b`-to-one parts:
`ValidKutinTriple n m a b`), let `P(m, a, b) := E_{σ,τ}[p({δ^{στ}_ij})]`, the average over all
pairs of permutations `σ, τ` of `{1, …, n}` of `p` evaluated at the indicator variables of the
input `x^{στ}_i = τ(x^{m,a,b}_{σ(i)})` (`kutinAverage p m a b`). Then `P` is a polynomial in
`m, a, b` with `deg P ≤ deg p`.

"`P` is a polynomial" is read as: there is a real trivariate polynomial `Q` of total degree at
most the total degree of `p` with `Q(m, a, b) = P(m, a, b)` at every valid triple (the domain on
which `P` is defined). Indices are 0-based in Lean (`Fin n`); `kutinInput` keeps the source's
1-based formulas `⌈i/a⌉` and `n − ⌊(n − i)/b⌋` and shifts the value by one. `p` is an arbitrary
polynomial (not necessarily multilinear), as in the source. -/
theorem kutin_average_isPolynomial (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℝ) :
    ∃ Q : MvPolynomial (Fin 3) ℝ, Q.totalDegree ≤ p.totalDegree ∧
      ∀ m a b : ℕ, ValidKutinTriple n m a b →
        MvPolynomial.eval ![(m : ℝ), (a : ℝ), (b : ℝ)] Q = kutinAverage p m a b := by
  sorry

end QAlgorithms.Childs
