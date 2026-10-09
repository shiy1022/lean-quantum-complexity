import QAlgorithms.Defs.Query

/-!
# de Wolf, Chapter 2: the Deutsch–Jozsa and Bernstein–Vazirani algorithms

R. de Wolf, *Quantum Computing: Lecture Notes*, §2.4.1–§2.4.2 (PDF pp. 29–31).

The input `x ∈ {0,1}^N`, `N = 2^n`, is a function `x : Qubits n → Bool` (bit `x_i` addressed by
the `n`-bit index `i`). The algorithm is the fixed circuit `H^{⊗n} O_{x,±} H^{⊗n}` applied to
`|0^n⟩` (`deutschJozsaState x`), with the phase query `O_{x,±} : |i⟩ ↦ (−1)^{x_i}|i⟩`
(`phaseOracle x`), followed by a computational-basis measurement. The circuit makes one query
and uses `2n` Hadamard gates, and only the query depends on `x`.
-/

namespace QAlgorithms.DeWolf

/-- de Wolf §2.4.1 (PDF pp. 30–31), the Deutsch–Jozsa algorithm: for every `n` and every
`x ∈ {0,1}^{2^n}` that is constant or balanced, measuring `H^{⊗n} O_{x,±} H^{⊗n} |0^n⟩` yields
`0^n` with probability `1` if `x` is constant and with probability `0` if `x` is balanced
(`2 · |x| = 2^n`). So the rule "answer constant iff the outcome is `0^n`" decides the problem
with certainty using one phase query and `2n` Hadamard gates. -/
theorem deutschJozsa_exact (n : ℕ) (x : Qubits n → Bool) :
    (IsConstant x → prob (deutschJozsaState x) (fun _ : Fin n => false) = 1) ∧
      (IsBalanced x → prob (deutschJozsaState x) (fun _ : Fin n => false) = 0) := by
  sorry

/-- de Wolf §2.4.2 (PDF p. 31), the Bernstein–Vazirani algorithm: for every `n` and every hidden
string `a ∈ {0,1}^n`, on the input `x_i = (i · a) mod 2` the Deutsch–Jozsa circuit
`H^{⊗n} O_{x,±} H^{⊗n}` maps `|0^n⟩` to the basis state `|a⟩`, so the final measurement yields
`a` with probability `1` (one phase query, `2n` Hadamard gates). -/
theorem bernsteinVazirani_exact (n : ℕ) (a : Qubits n) :
    deutschJozsaState (bvInput a) = ket a ∧ prob (deutschJozsaState (bvInput a)) a = 1 := by
  sorry

end QAlgorithms.DeWolf
