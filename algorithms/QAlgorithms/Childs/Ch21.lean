import QAlgorithms.Defs.Polynomial

/-!
# Childs, Chapter 21: Query complexity and the polynomial method

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 21 (PDF pp. 105–109).
-/

namespace QAlgorithms.Childs

/-- **Childs, Lemma 21.1** (PDF p. 106; model §21.1, p. 105, and §21.2, (21.1), (21.3), p. 106).
The acceptance probability of a `t`-query quantum algorithm for a problem with black-box input
`x ∈ {0,1}^n` is a polynomial in `x_1, …, x_n` of degree at most `2t`.

The algorithm is a `QueryAlg (Fin n) Bool W t`: an `x`-independent unit start state on the query
register `|i, b⟩` (`i ∈ [n]`, `b ∈ {0,1}`) and a workspace `W`, and `x`-independent unitaries
`U_0, …, U_t`, with the oracle `O_x ⊗ I_W` between consecutive unitaries. The oracle is the phase
oracle (21.3) `O_x |i, b⟩ = (−1)^{b x_i} |i, b⟩` (`controlledPhaseOracle x`), the form the proof
uses in (21.6). The source's (21.1) has no unitary before the first query; the extra `U_0` changes
nothing, since `U_0 |ψ⟩` is again an arbitrary `x`-independent unit vector (take `U_0 = I` to
recover (21.1) exactly). Acceptance is a computational-basis measurement of the final state with
outcome in an arbitrary set `Acc` of basis states (the proof: "the probability of any basis state
(and hence the probability of success)"). The polynomial is chosen after the algorithm and `Acc`,
and the identity is required at every 0/1 point `x`. -/
theorem acceptanceProb_isPolynomial (n t : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Fin n) Bool W t) (Acc : Finset ((Fin n × Bool) × W)) :
    ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ x : Fin n → Bool,
        MvPolynomial.eval (boolPoint x) p =
          probEvent (A.finalState (controlledPhaseOracle x)) fun z => z ∈ Acc := by
  sorry

/-- **Childs, Lemma 21.2** (PDF p. 107). Given any `n`-variate multilinear polynomial `p`, let
`P(k) := E_{|x|=k}[p(x)]`, the average of `p` over the bit strings of Hamming weight `k`
(`weightAverage p k`), for `k ∈ {0, …, n}`. Then `P` is a polynomial with `deg P ≤ deg p`.

"`P` is a polynomial" is read as: there is a univariate real polynomial `Q` of degree at most the
total degree of `p` with `Q(k) = P(k)` for every `k ∈ {0, …, n}` (the domain on which `P` is
defined; for these `k` the average is over a nonempty set). -/
theorem symmetrization_isPolynomial (n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ p.totalDegree ∧
      ∀ k : ℕ, k ≤ n → Q.eval (k : ℝ) = weightAverage p k := by
  sorry

end QAlgorithms.Childs
