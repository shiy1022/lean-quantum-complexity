import QAlgorithms.Defs.LocalHamiltonian

/-!
# de Wolf, Chapter 14: QMA and the local Hamiltonian problem

R. de Wolf, *Quantum Computing: Lecture Notes*, §14.1–§14.3 (PDF pp.127–133).
-/

namespace QAlgorithms.DeWolf

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

/-- The `k`-local Hamiltonian promise problem of de Wolf §14.2, Definition 2 (PDF p.129), with
gap `b − a ≥ 1/g(n)`, restricted to the source's input convention of p.128, footnote 2: the
input length is larger than the number `n` of qubits (`n ≤ |encode I|`). The yes-instances
(`L₁`) have `λ_min(H) ≤ a`, the no-instances (`L₀`) have `λ_min(H) ≥ b`; all other strings form
`L_*`. Without the restriction `n ≤ |encode I|` an instance could name exponentially many
qubits (its length is only `≈ 2 log₂ n` in `n`), and `b − a ≥ 1/g(n)` would then allow a gap
exponentially small in the input length. -/
def lhProblem (k : ℕ) (g : Polynomial ℕ) : PromiseProblem where
  yes := {w | ∃ I : LocalHamiltonian.Instance k, w = LocalHamiltonian.encode I ∧ I.n ≤ w.length ∧ I.Valid g ∧
    minEigenvalue I.hamiltonian ≤ I.a}
  no := {w | (∃ I : LocalHamiltonian.Instance k, w = LocalHamiltonian.encode I ∧ I.n ≤ w.length ∧ I.Valid g ∧
      (I.b : ℝ) ≤ minEigenvalue I.hamiltonian) ∧
    ¬ ∃ I : LocalHamiltonian.Instance k, w = LocalHamiltonian.encode I ∧ I.n ≤ w.length ∧ I.Valid g ∧
      minEigenvalue I.hamiltonian ≤ I.a}
  disjoint := Set.disjoint_left.2 fun _ hy hn => hn.2 hy

/-- de Wolf §14.3 and §14.3.2 (PDF pp.130–133; Kitaev): for every `k ≥ 5`, the `k`-local
Hamiltonian problem is QMA-complete.

1. Membership: for every polynomial `g` (gap `b − a ≥ 1/g(n)`), the problem is in (promise) QMA.
2. Hardness: every promise problem in QMA Karp-reduces (polynomial time, `L₁ → L₁`,
   `L₀ → L₀`) to the `k`-local Hamiltonian problem for some polynomial gap `1/g(n)`; in the
   source's proof `b − a = 1/(4T(T+1))` with `T` the size of the verifier for the given problem.
-/
theorem localHamiltonian_qmaComplete (k : ℕ) (hk : 5 ≤ k) :
    (∀ g : Polynomial ℕ, lhProblem k g ∈ PromiseQMA) ∧
      ∀ L ∈ PromiseQMA, ∃ g : Polynomial ℕ, PromiseReduces L (lhProblem k g) := by
  sorry

end QAlgorithms.DeWolf
