import QAlgorithms.Defs.Query

/-!
# de Wolf, Chapter 3: Simon's algorithm

R. de Wolf, *Quantum Computing: Lecture Notes*, §3.1–§3.3 (PDF pp. 35–38).

`N = 2^n` and the index set `{0, …, N − 1}` is identified with `{0,1}^n = Qubits n`. The input
`x = (x_0, …, x_{N−1})` with `x_i ∈ {0,1}^n` is a function `x : Qubits n → Qubits n`; one query
returns the whole string `x_i`, in its unitary form `|i, y⟩ ↦ |i, y ⊕ x_i⟩` (`xorOracle x`).
Simon's promise "`x_i = x_j` iff `i = j` or `i = j ⊕ s`" is `SimonPromise x s`; the bitwise sum
`j ⊕ s` is `j + s` in `Fin n → Bool`. One run of the quantum subroutine is the fixed circuit
`(H^{⊗n} ⊗ I) O_x (H^{⊗n} ⊗ I)` applied to `|0^n⟩|0^n⟩` (`simonRunState x`), followed by a
measurement of the first register; the intermediate measurement of the second register is
"not necessary" (p. 36), so the first-register marginal is used.
-/

namespace QAlgorithms.DeWolf

/-- An `n`-bit string as a vector of `𝔽₂^n` (`ZMod 2`), so that linear (in)dependence of the
outcomes `j` "modulo 2" (de Wolf p. 36) can be expressed. -/
def simonBitsToZMod2 {n : ℕ} (b : Qubits n) : Fin n → ZMod 2 :=
  fun k => if b k then 1 else 0

/-- The dimension over `𝔽₂` of the span of the strings `l 0, …, l (m − 1)` (de Wolf p. 36:
"the j's you have generated at some point span a space of size `2^k`"; this is `k`). -/
noncomputable def simonSpanRank {m n : ℕ} (l : Fin m → Qubits n) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun k => simonBitsToZMod2 (l k)))

/-- de Wolf §3.2 (PDF pp. 35–36), Simon's algorithm. For every `n`, every input
`x : {0,1}^n → {0,1}^n` and every nonzero `s` with Simon's promise
(`x_i = x_j ⟺ i = j ∨ i = j ⊕ s`):

1. one run of the subroutine (`|0^n⟩|0^n⟩`, `H^{⊗n}` on the first register, one query,
   `H^{⊗n}` on the first register) yields first-register outcome `j` with probability
   `2/2^n = 2^{−(n−1)}` if `s · j = 0 mod 2` and `0` otherwise, i.e. a uniformly random element
   of `{j | s · j = 0 mod 2}`;
2. there are `C > 0` and `N₀`, independent of `n`, `x`, `s`, such that for `n ≥ N₀`, if the
   subroutine is repeated independently until the outcomes span a space of dimension `n − 1`,
   the expected number of runs (= expected number of `x_i`-queries, one per run) is at most
   `C · n` (the outcome distribution `μ` is the one of item 1);
3. whenever outcomes `j_1, …, j_m`, all orthogonal to `s`, span a space of dimension `≥ n − 1`,
   the only nonzero solution `y` of the equations `j_k · y = 0 mod 2` is `y = s`;
4. there are `C > 0` and `N₀` such that for every `n ≥ N₀` a classical Boolean circuit of size
   at most `C n^3` maps any `n − 1` linearly independent strings `j_1, …, j_{n−1}` orthogonal to
   a nonzero `s` to `s` (Gaussian elimination modulo 2, "a classical circuit of size roughly
   `O(n^3)`"). -/
theorem simon_algorithm :
    (∀ (n : ℕ) (x : Qubits n → Qubits n) (s : Qubits n), SimonPromise x s → s ≠ 0 →
      ∀ j : Qubits n, marginalFst (simonRunState x) j =
        if dotBits s j = false then 2 / (2 : ℝ) ^ n else 0) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (x : Qubits n → Qubits n) (s : Qubits n),
      SimonPromise x s → s ≠ 0 →
      ∃ μ : PMF (Qubits n), (∀ j, μ j = ENNReal.ofReal (marginalFst (simonRunState x) j)) ∧
        expectedStoppingTime μ (fun _ l => n - 1 ≤ simonSpanRank l) ≤
          ENNReal.ofReal (C * n)) ∧
    (∀ (n : ℕ) (s : Qubits n), s ≠ 0 → ∀ (m : ℕ) (js : Fin m → Qubits n),
      (∀ k, dotBits s (js k) = false) → n - 1 ≤ simonSpanRank js →
      ∀ y : Qubits n, y ≠ 0 → (∀ k, dotBits (js k) y = false) → y = s) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ G : BoolCircuit ((n - 1) * n) n,
      G.WellFormed ∧ (G.size : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
      ∀ (s : Qubits n), s ≠ 0 → ∀ js : Fin (n - 1) → Qubits n,
        (∀ k, dotBits s (js k) = false) →
        LinearIndependent (ZMod 2) (fun k => simonBitsToZMod2 (js k)) →
        G.eval (fun p => js (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) = s) := by
  sorry

/-- de Wolf §3.3.2 (PDF pp. 37–38), the classical lower bound for the decision version of
Simon's problem (where `s = 0^n` is also allowed; task: decide whether `s = 0^n`). There are
constants `c > 0` and `n₀` such that for every `n ≥ n₀`, every classical randomized algorithm
(a probability distribution over deterministic adaptive decision trees, each querying whole
strings `x_i` and making at most `T` queries on every input) that, on every input `x` satisfying
the promise with some `s`, outputs the answer `[s = 0^n]` with probability at least `2/3`, makes
`T ≥ c √(2^n)` queries. -/
theorem simon_classical_lowerBound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (T : ℕ) (R : RandDecisionTree (Qubits n) (Qubits n) Bool),
      RandMakesAtMost R T →
      (∀ (x : Qubits n → Qubits n) (s : Qubits n), SimonPromise x s →
        successProb R x (decide (s = 0)) ≥ 2 / 3) →
      c * Real.sqrt ((2 : ℝ) ^ n) ≤ T := by
  sorry

end QAlgorithms.DeWolf
