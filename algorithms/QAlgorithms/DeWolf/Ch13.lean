import QAlgorithms.Defs.Circuit

/-!
# de Wolf, Chapter 13: Quantum complexity theory

de Wolf §13.1 (PDF p.121): most Boolean functions need exponentially many gates. The node
§13.3 (BQP ⊆ PSPACE, PDF pp.122–125) is reused from `bqp-pspace` (`ShiBQP.bqp_subset_pspace`)
and has no Lean here.
-/

namespace QAlgorithms.DeWolf

/-- **Most functions need exponentially many gates** (de Wolf §13.1, PDF p.121).

Fix a finite set `S` of elementary gates, each a unitary acting on at most 3 qubits. A circuit
over `S` on the `n` input wires plus `w` workspace wires (initially `|0⟩`) computes
`f : {0,1}ⁿ → {0,1}` if for every input `x`, measuring the first qubit of the final state
`C|x, 0⟩` gives `f(x)` with probability at least `2/3` (`Circuit.ComputesBool`, output wire
`0`, the source's first qubit). If at least 1% of all `2^(2^n)` Boolean functions on `n` bits
are computable by circuits with at most `C` gates (any workspace), then `C ≥ Ω(2ⁿ/n)`: there
are `c > 0` and `n₀`, depending only on the gate set, with `C ≥ c · 2ⁿ / n` for all `n ≥ n₀`.

The size of a circuit is its number of gates; the source additionally counts the initial
qubits among its `C` gates, which only makes its `C` larger, so this gate-count form implies
the source's. -/
theorem most_functions_need_exponential_gates (S : Set Gate) (hS : S.Finite)
    (hunit : ∀ g ∈ S, g.IsUnitary) (harity : ∀ g ∈ S, g.arity ≤ 3) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (hn : 0 < n), n₀ ≤ n → ∀ C : ℕ,
      2 ^ (2 ^ n) ≤ 100 * Set.ncard {f : Qubits n → Bool | ∃ (w : ℕ) (circ : Circuit S (n + w)),
        circ.size ≤ C ∧ circ.ComputesBool (Fin.castAdd w (⟨0, hn⟩ : Fin n)) f} →
      c * ((2 : ℝ) ^ n / n) ≤ C := by sorry

end QAlgorithms.DeWolf
