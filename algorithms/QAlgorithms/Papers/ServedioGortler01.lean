import QAlgorithms.Defs.LearningSeparation

/-!
# Servedio, Gortler, *Quantum versus classical learnability*

R. A. Servedio, S. J. Gortler, arXiv:quant-ph/0007036v1, cited "SG p.N" (PDF pages).

* Lemmas 4, 8 and 11 (§§3.2.1, 3.2.2, 3.3, pp.6, 8, 9; proofs in Appendix A, p.14): the classical
  membership-query complexity of exact learning a class `C` of concepts over `{0,1}^n`, in terms
  of `γ̂^C` (frozen `gammaParam`) and `log |C|`.
* Observations 17 and 18 (§5, p.12): under the hardness of factoring Blum integers (p.11), a
  separation between efficient quantum and classical learnability (PAC, and exact from
  membership queries).

The learning models are the frozen ones of `QAlgorithms.Defs.Learning` and
`QAlgorithms.Defs.LearningSeparation` (SG §§2.1–2.3, 3.1, 4.1).
-/

namespace QAlgorithms.Papers.ServedioGortler01

open QAlgorithms.Learning

/-- SG, Lemmas 4, 8 and 11 (pp.6, 8, 9; proofs in Appendix A, p.14). §3.2 writes `C` for a single
class `C_n` of concepts over `{0,1}^n` (p.4), so the constants are absolute: each is chosen before
`n` and `C`.

Let `T(C)` be the classical sample complexity of exact learning `C` from membership queries
(`classicalExactComplexity C`: the least `T` such that some randomized algorithm, i.e. a
probability distribution over adaptive query trees, making at most `T` queries outputs the target
`c` with probability `≥ 2/3` for every `c ∈ C`), and let `γ̂^C` be the parameter of p.6
(`gammaParam C`), defined for `|C| ≥ 2`.
1. (Lemma 4) `T(C) = Ω(1/γ̂^C)`: `T(C) ≥ K / γ̂^C` whenever `|C| ≥ 2`.
2. (Lemma 8) `T(C) = Ω(log |C|)`: `T(C) ≥ K log₂ |C|`.
3. (Lemma 11) `T(C) = O(log |C| / γ̂^C)`: `T(C) ≤ K log₂ |C| / γ̂^C` whenever `|C| ≥ 2`.

The hypothesis `|C| ≥ 2` is where `γ̂^C` is defined (otherwise `gammaParam` is the junk value `0`).
In (2) no size hypothesis is needed: `log₂ 0 = log₂ 1 = 0` in Lean. `classicalExactComplexity`
bounds the number of queries on every input string, the source only on targets `c ∈ C`; the two
complexities coincide (prune each tree at depth `T`). The output is the hypothesis function itself,
which is the source's "representation of a circuit `h` with `h ≡ c`" up to an encoding. -/
theorem classicalExact_gamma_logSize_bounds :
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
        K / gammaParam C ≤ (classicalExactComplexity C : ℝ)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)),
        K * Real.logb 2 (C.card : ℝ) ≤ (classicalExactComplexity C : ℝ)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
        (classicalExactComplexity C : ℝ) ≤ K * Real.logb 2 (C.card : ℝ) / gammaParam C) := by
  sorry

/-- SG, Observation 17 (p.12), with the hardness hypothesis of p.11.

If no polynomial-time classical randomized algorithm factors a uniformly random Blum integer
`N = pq` (`p ≠ q` `ℓ`-bit primes, `p ≡ q ≡ 3 (mod 4)`) with non-negligible success probability
(`FactoringBlumHard`), then there is a concept class `C = (C_n)_n` that is efficiently quantum PAC
learnable (a family of `{H, T, CNOT}` networks with QEX gates at the bottom, of size polynomial in
`n, 1/ε, 1/δ`, outputting a circuit that is an `ε`-approximator of `c` under `D` with probability
`≥ 1 − δ`, for every `c ∈ C_n` and every distribution `D`) but not efficiently classically PAC
learnable (no polynomial-time probabilistic Turing machine does the same from `EX(c, D)`).

Accuracy and confidence enter as `ε = 1/a`, `δ = 1/b` with integers `a, b ≥ 2`, which is
equivalent to the source's real `ε, δ ∈ (0, 1)` up to polynomial factors.

As in the source (p.10), the quantum learner is a non-uniform family of networks while the
classical learner is a uniform machine. -/
theorem quantumPAC_separation (hfact : FactoringBlumHard) :
    ∃ C : (n : ℕ) → Set (Qubits n → Bool),
      EffQuantumPACLearnable C ∧ ¬ EffClassicalPACLearnable C := by
  sorry

/-- SG, Observation 18 (p.12), with the hardness hypothesis of p.11.

If no polynomial-time classical randomized algorithm factors a uniformly random Blum integer with
non-negligible success probability (`FactoringBlumHard`), then there is a concept class
`C = (C_n)_n` that is efficiently quantum exact learnable from membership queries (a family of
`{H, T, CNOT}` networks with `QMQ_c` gates, of size polynomial in `n`, fixed independently of the
target, outputting a circuit `h ≡ c` with probability `≥ 2/3` for every `c ∈ C_n`) but not
efficiently classically exact learnable from membership queries (no polynomial-time probabilistic
Turing machine with `MQ_c` does the same).

As in the source (p.5), the quantum learner is a non-uniform family of networks while the
classical learner is a uniform machine. -/
theorem quantumExact_separation (hfact : FactoringBlumHard) :
    ∃ C : (n : ℕ) → Set (Qubits n → Bool),
      EffQuantumExactLearnable C ∧ ¬ EffClassicalExactLearnable C := by
  sorry

end QAlgorithms.Papers.ServedioGortler01
