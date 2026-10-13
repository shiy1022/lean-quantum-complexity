import QAlgorithms.Defs.EsscherOracleCircuits

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA09

open QAlgorithms.QuantumEsscher

/-- Proposition 12, arXiv:2401.07561v2, PDF p.15: the density signal obtained from
purified access, flattened with purification ancillas first and the signal system last.
This only reindexes the frozen `densityEncoding`; it introduces no accuracy assumption. -/
def purifiedDensitySignal (P : PublicParameters)
    (purification : Matrix.unitaryGroup (Qubits (P.purificationAncillas + P.n)) ℂ) :
    Matrix (Qubits (externalWidths P 0)) (Qubits (externalWidths P 0)) ℂ :=
  castOperator (by simp [externalWidths]; omega)
    ((densityEncoding purification).submatrix
      (qubitsAppendEquiv (P.purificationAncillas + P.n) P.n)
      (qubitsAppendEquiv (P.purificationAncillas + P.n) P.n))

/-- Theorem 5, arXiv:2401.07561v2, PDF pp.6–7, Algorithm 1 (called Algorithm III A
in the prose). The public QEsscher construction precedes all hidden inputs and oracle
completions. The target is the absolute operator-norm block-encoding of the subnormalized
transform, and every ordinary, adjoint or controlled oracle call is counted.

Source corrections: the box and Step 3 print `b = ceil(log_2 d)`, despite requiring
`d + 1 <= 2^b`; use `Nat.clog 2 (d + 1)`. The box prints the divisor `exp(beta)`,
whereas proof Step 5 explicitly gives `4 * exp(beta)`; use the latter. Logarithms remain
base 2 and the matrix exponential remains the natural exponential.

The printed `epsBE = (eps / (8 * log_2(1/eps)))^2` is retained. Equation (III.2)
requires a quantitative degree bound absent from the printed big-O estimate; this is
an unresolved proof gap, not an extra hypothesis or a field of the construction.
The p.9 `n_rho = poly(n)` convention is a family access convention; this query-only
statement keeps its actual ancillary size and asserts no gate-time bound. -/
theorem quantumEsscherTransform_implementation :
    ∃ Cdensity Cobservable : ℝ, 0 < Cdensity ∧ 0 < Cobservable ∧
      ∃ overhead : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
        ∀ P : PublicParameters, P.eps ≤ eps0 →
          ∃ construction : Construction P,
            (construction.circuit.queryCount 0 : ℝ) ≤
              Cdensity * P.kappa * (Real.logb 2 P.eps⁻¹) ^ 2 *
                max 1 (Real.logb 2 (2 + P.kappa * (Real.logb 2 P.eps⁻¹) ^ 2)) ^ overhead ∧
            (∀ j : Fin P.d, (construction.circuit.queryCount j.succ : ℝ) ≤
              Cobservable * Real.logb 2 P.eps⁻¹) ∧
            ∀ (input : InputData P)
              (purification : Matrix.unitaryGroup (Qubits (P.purificationAncillas + P.n)) ℂ),
              IsPurifiedAccess (a := P.purificationAncillas) input.rho
                (purification : Matrix (Qubits (P.purificationAncillas + P.n))
                  (Qubits (P.purificationAncillas + P.n)) ℂ) →
              ∀ O : (k : Fin (P.d + 1)) →
                  Matrix (Qubits (externalWidths P k)) (Qubits (externalWidths P k)) ℂ,
                O 0 = purifiedDensitySignal P purification →
                (∀ j : Fin P.d, IsQubitBlockEncoding P.observableAncillas P.n
                  (castOperator (by simp [externalWidths]) (O j.succ))
                  1 P.encodingError (input.H j)) →
                IsQubitBlockEncoding P.outputAncillas P.n (construction.circuit.unitary O)
                  1 P.eps (subnormalizedTransform P input) := by sorry

end QAlgorithms.Papers.RoadmapA09

