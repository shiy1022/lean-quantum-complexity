import QAlgorithms.Defs.FixedPointSearch
import QAlgorithms.Defs.CircuitResources

noncomputable section

namespace QAlgorithms.Papers.RoadmapA14

/-- Yoder, Low, Chuang, arXiv:1409.3305v2, PDF p.1 Eq. (1), p.2 guaranteed
interval, and p.3 Eqs. (10)--(11) and Fig.2. For every odd length `L = 2*l+1`
and tolerance `delta` in `[0,1]`, one input-independent circuit implements the
explicit phase sequence up to global phase, with `L-1` plain target-flip queries,
one reusable clean ancilla, and an absolute quadratic elementary-gate overhead.
The success identity and uniform error bound include the continuous endpoint
`delta = 0` (p.4); neither the identity nor sequence unitarity is assumed.
The target projector avoids the inconsistent rephasing of Eq. (4) on p.2.
-/
theorem fixedPointSearch_exact :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n l : ℕ) (delta : ℝ), 0 ≤ delta → delta ≤ 1 →
        ∃ c : OracleCircuit singleQubitCnotGateSet ![n, n + 1] (n + 1),
          c.queryCount 1 = 2 * l ∧ c.controlledQueryCount 1 = 0 ∧
          c.queryCount 0 = 2 * l ∧ c.controlledQueryCount 0 = 0 ∧
          (c.gateCount : ℝ) ≤ C * (l : ℝ) * ((n : ℝ) + 1) ^ 2 ∧
          ∀ (A : Matrix (Qubits n) (Qubits n) ℂ)
            (T : EuclideanSpace ℂ (Qubits n))
            (U : Matrix (Qubits n × Bool) (Qubits n × Bool) ℂ),
            A ∈ Matrix.unitaryGroup (Qubits n) ℂ → IsTargetFlipOracle T U →
            inner ℂ T (act A (zeroKet n)) ≠ 0 →
            let s := act A (zeroKet n)
            let lam := ‖inner ℂ T s‖ ^ 2
            let O : (k : Fin 2) → Matrix (Qubits (![n, n + 1] k))
                (Qubits (![n, n + 1] k)) ℂ :=
              Fin.cases A (Fin.cases (U.submatrix
                (fun z : Qubits (n + 1) => (Fin.init z, z (Fin.last n)))
                (fun z : Qubits (n + 1) => (Fin.init z, z (Fin.last n))))
                (fun k : Fin 0 => Fin.elim0 k))
            let phi := act (c.unitary O) (zeroAncillaVec s 1)
            (∃ theta : ℝ, ImplementsWithCleanAncillas (c.unitary O)
              (Complex.exp (Complex.I * (theta : ℂ)) • fixedPointSequence l delta A T)) ∧
            ‖inner ℂ T (act (fixedPointSequence l delta A T) s)‖ ^ 2 =
              fixedPointProfile l lam delta ∧
            ‖inner ℂ (zeroAncillaVec T 1) phi‖ ^ 2 = fixedPointProfile l lam delta ∧
            (fixedPointWidth l delta ≤ lam →
              1 - delta ^ 2 ≤ ‖inner ℂ (zeroAncillaVec T 1) phi‖ ^ 2) := by sorry

end QAlgorithms.Papers.RoadmapA14

