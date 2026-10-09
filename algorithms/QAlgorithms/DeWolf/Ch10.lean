import QAlgorithms.Defs.LinearSystems

/-!
# de Wolf, Chapter 10: the HHL algorithm

de Wolf §10.1–10.3 (PDF pp.95–98) states the HHL bounds only roughly ("roughly `κ²s/ε` queries").
The topic node is therefore stated as Childs–Kothari–Somma 2017 (arXiv:1511.02306v2, cited
"CKS p.N", PDF pages): Problem 1 (QLSP, CKS p.3) and Theorem 2 (HHL algorithm, CKS p.4), in the
cost model of CKS p.3 (query complexity = uses of `P_A`; gate complexity = number of 2-qubit
gates; gate-efficient = gate complexity `O(Q poly(log Q, log N))`).
-/

namespace QAlgorithms.DeWolf

/-- CKS p.3 ("by gate complexity, we mean the total number of 2-qubit gates used in the
algorithm"): the gate set of all 2-qubit unitary gates. Chunk-local. -/
def twoQubitGates : Set Gate :=
  {g | g.arity = 2 ∧ g.IsUnitary}

/-- The register sizes of the three black boxes of the QLSP for an `N × N` matrix whose entries
are written in `b` bits, with `n = ⌈log₂ N⌉`: black box `0` is the column map (1) of `P_A`
(`2n` qubits), black box `1` is the entry map (2) of `P_A` (`2n + b` qubits), black box `2` is
`P_B` (`n` qubits). Chunk-local. -/
def qlspArity (N b : ℕ) : Fin 3 → ℕ :=
  ![Nat.clog 2 N + Nat.clog 2 N, Nat.clog 2 N + Nat.clog 2 N + b, Nat.clog 2 N]

/-- **The HHL algorithm** (de Wolf §10.2–10.3, PDF p.96; stated as CKS Problem 1, p.3, and
Theorem 2, p.4): the QLSP can be solved by a gate-efficient algorithm that makes
`O((dκ²/ε) poly(log(dκ/ε)))` queries to `P_A` and `O(dκ poly(log(dκ/ε)))` uses of `P_B`.

Quantifier order: the constants `C, c` of the two query bounds are absolute (before everything);
the constants `C', c'` of the gate-efficiency bound may depend on the fixed exact encoding
`dec : {0,1}^b → ℂ` of matrix entries (CKS p.3: "we assume the entries of `A` can be represented
exactly"); then for all parameters `N, d, κ, ε` there is one oracle circuit (it may depend on
`N, d, κ, ε` and the encoding, never on `A`, `b⃗` or the oracles) that meets the three cost bounds
and succeeds on every QLSP instance with these parameters. Queries may be controlled or inverted
(each counts as one use). The output layout is a flag wire, `⌈log₂ N⌉` output wires, `m` garbage
wires, started in `|0…0⟩`; success is `QLSPSuccess` (flag probability `≥ 1/2`, flagged branch
`ε`-close to `|x⟩ ⊗ |garbage⟩`). -/
theorem hhl_cks_theorem2 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
    ∀ (b : ℕ) (dec : Qubits b → ℂ),
    ∃ C' : ℝ, 0 < C' ∧ ∃ c' : ℕ,
    ∀ (N d : ℕ) (κ ε : ℝ), 1 ≤ d → 1 ≤ κ → 0 < ε → ε < 1 →
    ∃ (m : ℕ) (alg : OracleCircuit twoQubitGates (qlspArity N b) (1 + Nat.clog 2 N + m)),
      ((alg.queryCount 0 + alg.queryCount 1 : ℕ) : ℝ) ≤
          C * ((d : ℝ) * κ ^ 2 / ε) * (1 + Real.log ((d : ℝ) * κ / ε)) ^ c ∧
      ((alg.queryCount 2 : ℕ) : ℝ) ≤
          C * ((d : ℝ) * κ) * (1 + Real.log ((d : ℝ) * κ / ε)) ^ c ∧
      ((alg.gateCount : ℕ) : ℝ) ≤
          C' * ((alg.queryCount 0 + alg.queryCount 1 : ℕ) : ℝ) *
            (1 + Real.log ((alg.queryCount 0 + alg.queryCount 1 : ℕ) : ℝ) + Real.log (N : ℝ)) ^ c' ∧
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (bvec : EuclideanSpace ℂ (Fin N))
        (orc : (k : Fin 3) → Matrix (Qubits (qlspArity N b k)) (Qubits (qlspArity N b k)) ℂ),
        A.IsHermitian → IsUnit A → conditionNumber A = κ → specNorm A = 1 → IsSparse A d →
        bvec ≠ 0 →
        IsSparseAccessOracle A d dec (orc 0) (orc 1) →
        IsStatePrep bvec (orc 2) →
        QLSPSuccess (act (alg.unitary orc) (zeroKet (1 + Nat.clog 2 N + m)))
          (padState (Nat.clog 2 N) (normalizedVec (act A⁻¹ bvec))) ε := by
  sorry

end QAlgorithms.DeWolf
