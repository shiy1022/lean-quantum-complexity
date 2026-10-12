import QAlgorithms.Defs.HDQIPreparation

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.RoadmapD07

/-- The coefficient input for Theorem 5's unit-cost arithmetic preprocessing.
Addresses below `m` contain the Hamiltonian coefficients, the next `l + 1`
addresses contain the polynomial coefficients, and all other addresses are zero.
No normalization factor, reference amplitudes, or gate entries are supplied. -/
def coefficientInput {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (l : ℕ) : ℕ → ℝ :=
  fun a => if h : a < m then c ⟨a, h⟩ else if a < m + (l + 1) then P.coeff (a - m) else 0

/-- Arithmetic programs may introduce only the constants `0`, `1`, and `-1`.
This prevents a chosen program from hiding precomputed reference or gate entries
in its constant instructions. Arithmetic and memory access have unit cost
(Lemma 4, arXiv:2601.18773v1, PDF pp.7-8). -/
def HasStandardConstants : ArithmeticProgram → Prop
  | .done => True
  | .step op rest =>
      (match op with
        | .constant _ v => v = 0 ∨ v = 1 ∨ v = -1
        | _ => True) ∧ HasStandardConstants rest
  | .loop _ body rest => HasStandardConstants body ∧ HasStandardConstants rest

/-- The computed MPS data of Eqs.(12)-(13), with bond dimension `l + 1`.
Address zero stores the normalization, followed by the two boundary vectors,
then the two local matrices for each term in row-major order. -/
def ComputesReferenceData {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (l : ℕ)
    (result : ℕ → ℝ) : Prop :=
  result 0 = hdqiReferenceNorm c P l ∧
    (∀ j : Fin (l + 1), (result (1 + j) : ℂ) = (hdqiReferenceMPS c P l).left j) ∧
    (∀ j : Fin (l + 1), (result (1 + (l + 1) + j) : ℂ) =
      (hdqiReferenceMPS c P l).right j) ∧
    ∀ (i : Fin m) (y : Fin 2) (j k : Fin (l + 1)),
      (result (1 + 2 * (l + 1) + ((i * 2 + y) * (l + 1) + j) * (l + 1) + k) : ℂ) =
        (hdqiReferenceMPS c P l).localMatrix i y j k

/-- Theorem 5 (arXiv:2601.18773v1, PDF pp.8-9), with the proof's necessary
corrections: real coefficients and the `j = 0,...,l` convention of Eqs.(10),(20);
`P(H) != 0` so Eq.(19) defines a density matrix; and decoder fixation of `|0,0>`
when its reference coefficient is nonzero, in addition to the positive-weight
action in Eq.(7). This is an additional guarantee, not a consequence of Eq.(7).
When that coefficient vanishes, no zero-branch action is imposed; in particular,
the identity-Pauli instance `H = I`, `P(x) = x` remains admissible.

The ordinary nonempty regime has `n,m >= 1`; degree zero is allowed. The
absolute constants, polynomial, and asymptotic thresholds precede every size
and coefficient. The concrete preparation, including its counted classical
computation, precedes every admissible decoder. The ideal model uses exact
one- and two-qubit gates and unit-cost real arithmetic/memory operations.

The reference normalization and normalized purification are conclusions, not
assumed resources. Pauli products retain their phases under the coherent Bell
basis change and its inverse (the proof's phase-suppressed display on p.9 is
read linearly). Preparation is exact, with no postselection. -/
theorem hamiltonianDQI_statePreparation :
    ∃ C : ℝ, 0 < C ∧ ∃ q : Polynomial ℕ, ∃ l0 : ℕ, 1 ≤ l0 ∧ ∃ s0 : ℕ,
      ∀ (n m l : ℕ), 1 ≤ n → 1 ≤ m →
      ∀ (labels : Fin m → CanonicalPauliLabel n) (c : Fin m → ℝ) (P : Polynomial ℝ),
        Function.Injective labels →
        (∀ i j, (canonicalPauli (labels i)).Commute (canonicalPauli (labels j))) →
        P.natDegree = l →
        Polynomial.aeval (pauliHamiltonian labels c) P ≠ 0 →
        (∃ D : Matrix (Qubits m × Qubits (n + n)) (Qubits m × Qubits (n + n)) ℂ,
          IsWeightDecoder labels l D ∧
            (parityMultinomialCoefficient c P l 0 ≠ 0 →
              act D (ket (0, 0)) = ket (0, 0))) →
        let H := pauliHamiltonian labels c
        let M : Matrix (Qubits n) (Qubits n) ℂ := Polynomial.aeval H P
        let N := hdqiReferenceNorm c P l
        let phi := ((N⁻¹ : ℝ) : ℂ) •
          act (Matrix.kronecker M (1 : Matrix (Qubits n) (Qubits n) ℂ)) (maxEntangled n)
        0 < N ∧ N ^ 2 = (M ^ 2).trace.re / (2 : ℝ) ^ n ∧
          0 < (M ^ 2).trace.re ∧ IsState (hdqiReference c P l) ∧
          IsState phi ∧ traceRight (pureDensity phi) = polynomialDensity H P ∧
          ∃ prep : HDQIPreparation n m,
            prep.classicalInput = coefficientInput c P l ∧
            HasStandardConstants prep.preprocessing ∧
            (∃ result, prep.preprocessing.eval prep.classicalInput = some result ∧
              ComputesReferenceData c P l result) ∧
            (l0 ≤ l → (prep.classicalCost : ℝ) ≤ C * m * (l : ℝ) ^ 3) ∧
            (s0 ≤ l + n →
              ((prep.circuit.length + m + (n + n) + prep.work : ℕ) : ℝ) ≤
                C * m * ((q.eval (l + n) : ℕ) : ℝ)) ∧
            prep.circuit.plainQueryCount 0 = 1 ∧
            prep.circuit.controlledQueryCount 0 = 0 ∧
            (∀ (k : Fin 1) (adj : Bool) (ctl : Option (Fin (m + (n + n) + prep.work)))
              (wires : Fin ((fun _ : Fin 1 => m + (n + n)) k) ↪
                Fin (m + (n + n) + prep.work))
              (hc : ∀ a, ctl = some a → a ∉ Set.range wires),
              OracleStep.query k adj ctl wires hc ∈ prep.circuit → adj = false ∧ ctl = none) ∧
            ∀ D : Matrix (Qubits m × Qubits (n + n)) (Qubits m × Qubits (n + n)) ℂ,
              IsWeightDecoder labels l D →
                (parityMultinomialCoefficient c P l 0 ≠ 0 →
                  act D (ket (0, 0)) = ket (0, 0)) →
                prep.output D = polynomialDensity H P := by sorry

end QAlgorithms.Papers.RoadmapD07