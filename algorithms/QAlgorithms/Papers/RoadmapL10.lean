import QAlgorithms.Defs.DirichletShadowLearning
import QAlgorithms.Defs.ShadowLearnerPrograms

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapL10

open GroundStateLearning

/-- The six single-qubit labels of Appendix A, PDF pp.12–13; true means spin up. -/
def shadowLabelCode (s : Axis × Bool) : Fin 6 :=
  match s with
  | (.X, false) => 0
  | (.X, true) => 1
  | (.Y, false) => 2
  | (.Y, true) => 3
  | (.Z, false) => 4
  | (.Z, true) => 5

/-- Parameter input to the compact-data loader (F32, F42, PDF pp.33,35). -/
def parameterInput {n m N : ℕ}
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n) : ℕ → ℝ :=
  fun address => ((List.ofFn fun l => List.ofFn (data l).1).flatten).getD address 0

/-- Label input to the loader: one of six outcomes per site, not a dense matrix (F32). -/
def labelInput {n m N : ℕ}
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n) : ℕ → Fin 6 :=
  fun address => ((List.ofFn fun l => List.ofFn fun j =>
    shadowLabelCode ((data l).2 j)).flatten).getD address 0

/-- Compact representation: m*N parameter words followed by n*N labels (F42). -/
def loadedTraining {n m N : ℕ} (load : LearnerProgram)
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n) : LearnerState :=
  learnerExecution (parameterInput data) (labelInput data) (fun _ => 0)
    load ⟨0, ∅, 0, false⟩

/-- Real and imaginary entries of supplied few-body operators in wire order (F45). -/
def fewBodyEntryInput {L : ℕ} (arity : Fin L → ℕ)
    (localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ) : ℕ → ℝ :=
  fun address => ((List.ofFn fun i => (List.ofFn fun a : Fin (2 ^ arity i) =>
    (List.ofFn fun b : Fin (2 ^ arity i) =>
      let entry := localOp i ((bitsEquivFin (arity i)).symm a)
        ((bitsEquivFin (arity i)).symm b)
      [entry.re, entry.im]).flatten).flatten).flatten).getD address 0

/-- Execute an actual arithmetic/RAM evaluator on loaded data (F43–F46).
Only the new parameter and the local observable entries are external inputs. -/
def evaluatedPrediction {n m N L : ℕ} (load : LearnerProgram) (evaluate : LearnerProgram)
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n)
    (x : EuclideanSpace ℝ (Fin m)) (arity : Fin L → ℕ)
    (localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ) : LearnerState :=
  learnerExecution (fun address => (List.ofFn x).getD address 0) (fun _ => 0)
    (fewBodyEntryInput arity localOp) evaluate
    { loadedTraining load data with work := 0, failed := false }

/-- F1 and F.5(c), PDF pp.29,36: normalized projector onto the whole ground eigenspace.
Zero outside the cube is only a measurable extension, never a prediction target there. -/
def targetGroundFamily {n m terms spatial : ℕ}
    (H : HamiltonianFamily n m terms spatial) (x : EuclideanSpace ℝ (Fin m)) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  if x ∈ parameterCube m then
    if h : (H.hamiltonian x).IsHermitian then groundDensity (H.hamiltonian x) h else 0
  else 0

/-- Theorem 1 (PDF p.4), detailed Theorem 3 (pp.29–30), F.5 (pp.36–39).
The named predictor is Eqs.(2),(E3),(F27), using one Pauli snapshot per training point.
F3 prints exact state labels instead: the shadow-labelled premise and explicit construction
determine the reading here; independent source moderation is required. No periodic parameter
boundary condition or Theorem-4 gradient conclusion is assumed. Lemma 2 has a boundary gap,
recorded in the unit audit; this declaration preserves the printed headline target.

Physical constants, observable locality and confidence precede uniform resource constants.
The norm budget is normalized to B >= 1 (any smaller budget can be enlarged to 1).
Public programs are chosen before the hidden family, training draw and test parameter.
The representation is the frozen predictor; computed program work counts its compact evaluation.
For each fixed subsystem the mean trace-norm error is at most sqrt(4^q * eps).
Setting eps = eta^2 / 4^q gives the informal error eta, with confidence 1-delta.
No simultaneous-all-observables or simultaneous-all-subsystems guarantee is asserted. -/
theorem learningGroundStateRepresentations
    (spatial locality q : ℕ) (hspatial : 0 < spatial)
    (radius bd cd gap delta : ℝ)
    (hradius : 0 ≤ radius) (hbd : 0 ≤ bd) (hcd : 0 ≤ cd) (hgap : 0 < gap)
    (hdelta : 0 < delta ∧ delta < 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ B eps : ℝ, 1 ≤ B → 0 < eps → eps ≤ 1 →
    ∃ m0 : ℕ, 2 ≤ m0 ∧ ∀ n m : ℕ, 0 < n → m0 ≤ m →
    ∃ N : ℕ, ∃ hN : 0 < N, ∃ Lambda : ℝ, ∃ hLambda : 0 ≤ Lambda,
    ∃ load : LearnerProgram,
    ∃ evaluate : (L : ℕ) → (arity : Fin L → ℕ) →
      ((i : Fin L) → Fin (arity i) ↪ Fin n) → LearnerProgram × ℕ,
    (N : ℝ) ≤ C * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps) ∧
    (∀ data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n,
      let trained := loadedTraining load data
      trained.failed = false ∧ trained.stored.card ≤ (n + m) * N ∧
      (trained.work : ℝ) ≤ C * ((n + m) * N : ℕ) ∧
      (trained.work : ℝ) ≤ C * (n + 1) * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps) ∧
      (∀ l : Fin N, ∀ j : Fin m, trained.memory (l.val * m + j.val) = (data l).1 j) ∧
      ∀ l : Fin N, ∀ j : Fin n,
        trained.memory (m * N + l.val * n + j.val) =
          (shadowLabelCode ((data l).2 j)).val) ∧
    (∀ (L : ℕ) (arity : Fin L → ℕ) (wires : (i : Fin L) → Fin (arity i) ↪ Fin n),
      (∀ i, arity i ≤ q) →
      ∀ localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ,
      (∀ i, (localOp i).IsHermitian) → (∑ i, specNorm (localOp i)) ≤ B →
      ∀ data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n,
      ∀ x : EuclideanSpace ℝ (Fin m), x ∈ parameterCube m →
        let result := evaluatedPrediction load (evaluate L arity wires).1 data x arity localOp
        result.failed = false ∧
        result.memory (evaluate L arity wires).2 =
          ((∑ i, embedOp (localOp i) (wires i)) * predictor hN Lambda hLambda data x).trace.re ∧
        (result.work : ℝ) ≤ C * (n + L) * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps) ∧
        (result.stored.card : ℝ) ≤
          C * (n + m + L) * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps)) ∧
    ∀ (terms : ℕ) (H : HamiltonianFamily n m terms spatial),
      H.geometry.cardinalityBound ≤ locality → H.geometry.radiusBound ≤ radius →
      H.geometry.bd ≤ bd → H.geometry.cd ≤ cd →
      (∀ j x, x ∈ parameterCube m → ContDiffAt ℝ ⊤ (H.term j) x) →
      (∀ x ∈ parameterCube m, HasExcitationGap (H.hamiltonian x) gap) →
      ∃ measurable : Measurable (targetGroundFamily H),
      ∃ states : ∀ x ∈ parameterCube m, IsDensityMatrix (targetGroundFamily H x),
      (∀ (L : ℕ) (arity : Fin L → ℕ) (wires : (i : Fin L) → Fin (arity i) ↪ Fin n),
        (∀ i, arity i ≤ q) →
        ∀ localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ,
        (∀ i, (localOp i).IsHermitian) → (∑ i, specNorm (localOp i)) ≤ B →
        trainingLaw (targetGroundFamily H) measurable states N
          {data | (∫⁻ x, ENNReal.ofReal
            (((∑ i, embedOp (localOp i) (wires i)) *
              (predictor hN Lambda hLambda data x - targetGroundFamily H x)).trace.re ^ 2)
              ∂parameterCubeLaw m) ≤ ENNReal.ofReal eps} ≥ ENNReal.ofReal (1 - delta)) ∧
      ∀ (r : ℕ) (w : Fin r ↪ Fin n), r ≤ q →
        trainingLaw (targetGroundFamily H) measurable states N
          {data | (∫⁻ x, ENNReal.ofReal
            (traceNorm (reducedOperator w
              (predictor hN Lambda hLambda data x - targetGroundFamily H x)))
              ∂parameterCubeLaw m) ≤
                ENNReal.ofReal (Real.sqrt ((4 : ℝ) ^ q * eps))} ≥
          ENNReal.ofReal (1 - delta) := by sorry

end QAlgorithms.Papers.RoadmapL10
