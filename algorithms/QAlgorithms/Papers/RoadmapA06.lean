import QAlgorithms.Defs.GeneralizedYK

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.RoadmapA06

/-- The state `omega^{RE}` of Eq. (45), arXiv:2405.06051v6, PDF p.12.
It is obtained from Eq. (9)'s normalized purification by tracing out `DB'`.
The finite indices of `R` and `B'` copy the bases of `A` and `B`. -/
def decouplingState {A B E D : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D]
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ) :
    Matrix (Fin A × Fin E) (Fin A × Fin E) ℂ :=
  traceRight ((pureDensity (communicationState V)).submatrix
    (fun p : (Fin A × Fin E) × (Fin D × Fin B) => (p.1.1, (p.1.2, p.2)))
    (fun p : (Fin A × Fin E) × (Fin D × Fin B) => (p.1.1, (p.1.2, p.2))))

/-- The chosen `U_F : ABF -> ED` in its input and output computational bases
(Eqs. (19)--(20), PDF p.6). Both sides are flattened most significant factor first.
The compatible layout is included in this operation, hence in its gate cost. -/
def dilationMatrix {A B E D F : ℕ}
    (layout : (Fin A × Fin B) × Fin F ≃ Fin E × Fin D)
    (U : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :
    Matrix (Fin (E * D)) (Fin ((A * B) * F)) ℂ :=
  U.submatrix finProdFinEquiv.symm
    (fun j : Fin ((A * B) * F) =>
      let p : Fin (A * B) × Fin F := finProdFinEquiv.symm j
      layout (finProdFinEquiv.symm p.1, p.2))

/-- `C(U_F)` of Theorem 4 (PDF p.12), using the single- and two-qubit
unitary gate model of p.4. Frozen `ChannelCircuit` explicitly embeds a finite
register of dimension `d` in `ceil(log_2 d)` qubits, initializes added qubits,
and discards garbage. The source permits polynomially many ancillary qubits:
`ancillaBudget` is one polynomial allowance, chosen before every instance in
the theorem, evaluated at the number of qubits of `ED`. The value is infinity
if there is no realization within that allowance; finiteness is a conclusion
below, not an assumption. -/
def dilationGateComplexity {A B E D F : ℕ}
    (ancillaBudget : Polynomial ℕ)
    (layout : (Fin A × Fin B) × Fin F ≃ Fin E × Fin D)
    (U : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) : ℕ∞ :=
  circuitComplexity (ancillaBudget.eval (Nat.clog 2 (E * D)))
    (conjSuperop (dilationMatrix layout U))

/-- Theorem 4, "Performance of the generalized YK decoder", arXiv:2405.06051v6
(5 March 2026), PDF p.12, Eqs. (45)--(48), including the right-column continuation.
The explicit decoder is frozen `ykDecoder`, Eq. (44), with preprocessing (35),
projectors (49)--(50), and the real two-projector QSVT (51)--(53) (pp.10--13).
The error is half the trace norm on the preserved maximally entangled state.
The eigenvalue is the smallest NONZERO eigenvalue; full rank is not required.
The logarithm in (46) is natural, following the Lambert-W argument on p.9;
the qubit resource logarithm is base two. The polynomial ancillary allowance
of the standing gate model (p.4) and universal gate and ancilla constants are
chosen before all instances, and the same phases have both guarantees.
The resource bounds are the joint implementation bounds (167)--(168), p.25;
one-dimensional output is retained (discarding the input costs zero gates).
Only the receiver's `DB'` systems enter the decoder's circuit realization. -/
theorem generalizedYK_performance :
    ∃ ancillaBudget : Polynomial ℕ,
    ∃ gateConstant ancillaConstant : ℝ, 0 < gateConstant ∧ 0 < ancillaConstant ∧
      ∀ (A B E D F : ℕ) [NeZero A] [NeZero B] [NeZero E] [NeZero D] [NeZero F],
      ∀ (Phi : Superop (Fin A × Fin B) (Fin D))
        (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ)
        (layout : (Fin A × Fin B) × Fin F ≃ Fin E × Fin D)
        (U : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ),
      IsChannel Phi → IsChosenDilation Phi V layout U →
      ∀ (eps delta : ℝ) (t : ℕ),
      (∃ tau : Matrix (Fin E) (Fin E) ℂ, IsDensityMatrix tau ∧
        traceNorm (decouplingState V -
          Matrix.kronecker ((A : ℂ)⁻¹ • (1 : Matrix (Fin A) (Fin A) ℂ)) tau) ≤ eps) →
      0 < delta → delta < 1 → Odd t →
      ⌈16 * Real.exp 1 *
        Real.sqrt ((D : ℝ) / ((B : ℝ) * minPositiveEigenvalue (decouplingState V))) *
        Real.log (2 / delta)⌉₊ ≤ t →
      ∃ phi : Fin t → ℝ,
        (∀ j, -Real.pi < phi j ∧ phi j ≤ Real.pi) ∧
        recoveryError V (ykDecoder V phi) ≤ Real.sqrt eps + delta ∧
        ∃ unitaryGates : ℕ,
          dilationGateComplexity ancillaBudget layout U = (unitaryGates : ℕ∞) ∧
          ∃ decoderCircuit : ChannelCircuit (D * B) A,
            ExactChannelRealization
              (fun X => ykDecoder V phi (X.submatrix finProdFinEquiv finProdFinEquiv))
              decoderCircuit ∧
            (decoderCircuit.circuit.size : ℝ) ≤ gateConstant * (t : ℝ) *
              ((unitaryGates : ℝ) + Real.logb 2 ((D : ℝ) ^ 2 * (E : ℝ) / (B : ℝ))) ∧
            (decoderCircuit.added : ℝ) ≤
              ancillaConstant * Real.logb 2 ((D : ℝ) ^ 2 * (E : ℝ) / (B : ℝ)) := by sorry

end QAlgorithms.Papers.RoadmapA06
