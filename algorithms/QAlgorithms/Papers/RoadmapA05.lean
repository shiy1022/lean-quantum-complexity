import QAlgorithms.Defs.MatrixQSVTCircuits

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.RoadmapA05

open QAlgorithms.MatrixQSVT

/-- Lu, Liu and Lin, arXiv:2408.01439v4, Theorem 10, PDF pp. 7-8,
Eq. (38), with proof through p. 9: simultaneous complex matrix singular-value
transformation by an oracle-independent synthesis with exactly `d` alternating,
uncontrolled calls to `U` and its adjoint.

`PolynomialData` makes explicit the entrywise degree bound and common parity
used by Theorem 2 and Lemmas 8 and 11, but omitted from the printed Theorem 10.
The output uses the input signal space for even `d` and the output signal space
for odd `d`, correcting the repeated output `|0>` in Eq. (38) and the reversed
singular-vector labels in Eq. (2), consistently with Eqs. (1), (31)-(35).
The projector order follows these equations rather than the reversed labels
in the Fig. 3 caption: input at even stages, output at odd stages.
The contraction hypothesis is the printed matrix positivity condition; no
polynomial completion is assumed. Rectangular polynomial blocks are padded via
known row and column embeddings in `P`. All flag-zero coordinates, including
those outside the selected output embedding, are fixed by `IsFlaggedRealization`.
The equality holds on every input vector and has normalization one and error zero.
Degree zero, zero-qubit mixing registers, zero polynomials, and singular blocks
are allowed. No gate-count, classical synthesis-time, or success-probability
lower bound is claimed. -/
theorem matrixQSVT_synthesis
    {r c d : ℕ} (P : PolynomialData r c d)
    (hcontract : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ((1 : Matrix (Fin c) (Fin c) ℂ) - (P.eval x)ᴴ * P.eval x).PosSemidef)
    (I O K : Type) [Fintype I] [Fintype O] [Fintype K]
    [Nonempty I] [Nonempty O] [Nonempty K]
    [DecidableEq I] [DecidableEq O] [DecidableEq K]
    (input : I ↪ K) (output : O ↪ K) :
    ∃ S : SynthesisData I O K (P.mixingQubits + 1) d,
      S.input = input ∧ S.output = output ∧
      ∃ mixingLayout : Qubits (P.mixingQubits + 1) ≃ Bool × Qubits P.mixingQubits,
        S.circuit.queryCount 0 = d ∧
        ∀ (U : Matrix K K ℂ) (A : Matrix O I ℂ),
          IsRectangularEncoding input output U A →
          IsFlaggedRealization P S mixingLayout U A := by sorry

end QAlgorithms.Papers.RoadmapA05
