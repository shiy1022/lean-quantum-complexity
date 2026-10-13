import QAlgorithms.Defs.CKSFourierPrograms
import QAlgorithms.Defs.RetainedQueryPrograms

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.RoadmapA10

open QAlgorithms

attribute [local instance] Classical.propDecidable

/-- The logarithm convention explicitly required on CKS PDF p.15. -/
def precisionLog (kappa eps : ℝ) : ℝ := max 1 (Real.log (kappa / eps))

/-- Problem 1, CKS PDF p.3, with the permitted condition-number upper bound. -/
def MatrixPromise {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (kappa : ℝ) : Prop :=
  A.IsHermitian ∧ IsUnit A ∧ specNorm A = 1 ∧ conditionNumber A ≤ kappa

/-- The reduction's two black boxes: coherent SELECT with scratch, and coherent P_B with
its possibly nonzero, unentangled preparation workspace (CKS pp.3,7–8,12). -/
def reductionRegisters (N w s : ℕ) (G : CKSFourier.Grid) : Fin 2 → Type :=
  fun k => if k = 0 then (G.Index × Fin N) × Qubits s else Qubits (Nat.clog 2 N + w)

instance reductionFintype (N w s : ℕ) (G : CKSFourier.Grid) (k : Fin 2) :
    Fintype (reductionRegisters N w s G k) := by
  unfold reductionRegisters
  split_ifs <;> infer_instance

instance reductionDecidableEq (N w s : ℕ) (G : CKSFourier.Grid) (k : Fin 2) :
    DecidableEq (reductionRegisters N w s G k) := Classical.decEq _

/-- A bounded adaptive reduction. Its state, operations and measurements are fixed before
the hidden matrix, vector and oracle implementations. -/
structure FourierReduction (N w s : ℕ) (G : CKSFourier.Grid) where
  dimension : ℕ
  workspace : ℕ
  layout : Fin dimension ≃ Fin N × Fin workspace
  start : EuclideanSpace ℂ (Fin dimension)
  normalized : IsState start
  program : RetainedOracle.QueryProgram (reductionRegisters N w s G) (fun _ => false)
    (Fin dimension)

/-- Package the subroutines without making their entries available to fixed operations. -/
def reductionOracles {N w s : ℕ} {G : CKSFourier.Grid}
    (V : Matrix ((G.Index × Fin N) × Qubits s) ((G.Index × Fin N) × Qubits s) ℂ)
    (PB : Matrix (Qubits (Nat.clog 2 N + w)) (Qubits (Nat.clog 2 N + w)) ℂ) :
    (k : Fin 2) → Matrix (reductionRegisters N w s G k) (reductionRegisters N w s G k) ℂ :=
  fun k => if h : k = 0 then by simpa [reductionRegisters, h] using V
    else by simpa [reductionRegisters, h] using PB

/-- The simulated LCU block times its coefficient mass (CKS (18),(29),(52)).
This pins the output vector's phase, rather than optimizing over global phase.
Simulator scratch is initialized and postselected to zero. -/
def simulatedInverse {N s : ℕ} (G : CKSFourier.Grid)
    (V : Matrix ((G.Index × Fin N) × Qubits s) ((G.Index × Fin N) × Qubits s) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => (CKSFourier.coefficientMass G : ℂ) *
    ∑ a : G.Index, ∑ b : G.Index,
      star (CKSFourier.coefficientState G a) * V ((a, i), 0) ((b, j), 0) *
        CKSFourier.coefficientState G b

/-- A flagged pure output with probability at least one half and the direct vector error
of Problem 1, CKS p.3. The representative is specified separately. -/
def PureFlaggedOutput {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : IsUnit A) (b : EuclideanSpace ℂ (Fin N)) (hb : b ≠ 0)
    (representative : EuclideanSpace ℂ (Fin N))
    (success failure : Matrix (Fin N) (Fin N) ℂ) (eps : ℝ) : Prop :=
  success.PosSemidef ∧ failure.PosSemidef ∧ success.trace.re + failure.trace.re = 1 ∧
    1 / 2 ≤ success.trace.re ∧ IsState representative ∧
    ‖representative - linearSystemSolution hN A hA b hb‖ ≤ eps ∧
    success = (success.trace.re : ℂ) • pureDensity representative

/-- Both operations of P_A (CKS (1)–(2)) and P_B have separate counters. -/
def sparseWidths (N b w : ℕ) : Fin 3 → ℕ :=
  ![Nat.clog 2 N + Nat.clog 2 N, Nat.clog 2 N + Nat.clog 2 N + b, Nat.clog 2 N + w]

/-- Finite capped attempts, a computational success test, and retained quantum output.
An unsuccessful attempt is discarded before the next fresh attempt. -/
structure SparseFourierSolver (N b w : ℕ) where
  qubits : ℕ
  garbage : ℕ
  layout : Qubits qubits ≃ Qubits (Nat.clog 2 N) × Qubits garbage
  outputWires : Fin (Nat.clog 2 N) ↪ Fin qubits
  garbageWires : Fin garbage ↪ Fin qubits
  layout_eq : ∀ z, layout z = (z ∘ outputWires, z ∘ garbageWires)
  successWires : Finset (Fin qubits)
  attempts : List (OracleCircuit oneTwoQubitGateSet (sparseWidths N b w) qubits)
  uncontrolled : ∀ c ∈ attempts, ∀ step ∈ c, match step with
    | .gate _ => True
    | .query _ _ control _ _ => control = none

/-- The computational zero-outcome projector for the success flag. -/
def SparseFourierSolver.successProjector {N b w : ℕ} (S : SparseFourierSolver N b w) :
    Matrix (Qubits S.qubits) (Qubits S.qubits) ℂ :=
  Matrix.diagonal fun z => if ∀ q ∈ S.successWires, z q = false then 1 else 0

/-- Successful state of the capped restart routine. Each term is weighted by the probability
that all previous fresh attempts failed; CKS Corollary 10, pp.9–10. -/
def SparseFourierSolver.successState {N b w : ℕ} (S : SparseFourierSolver N b w)
    (O : (k : Fin 3) → Matrix (Qubits (sparseWidths N b w k)) (Qubits (sparseWidths N b w k)) ℂ) :
    List (OracleCircuit oneTwoQubitGateSet (sparseWidths N b w) S.qubits) →
      Matrix (Qubits S.qubits) (Qubits S.qubits) ℂ
  | [] => 0
  | c :: rest =>
      let rho := conjSuperop (c.unitary O) (pureDensity (zeroKet S.qubits))
      let good := conjSuperop S.successProjector rho
      good + ((1 - good.trace.re : ℝ) : ℂ) • S.successState O rest

/-- Decode only the valid N-dimensional subspace: discarded padding cannot count as success. -/
def SparseFourierSolver.output {N b w : ℕ} (S : SparseFourierSolver N b w)
    (O : (k : Fin 3) → Matrix (Qubits (sparseWidths N b w k)) (Qubits (sparseWidths N b w k)) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let J := finiteRegisterEmbedding N
  Jᴴ * traceRight ((S.successState O S.attempts).submatrix S.layout.symm S.layout.symm) * J

/-- Actual oracle applications summed over all capped attempts: a worst-case upper bound. -/
def SparseFourierSolver.queries {N b w : ℕ} (S : SparseFourierSolver N b w) (k : Fin 3) : ℕ :=
  (S.attempts.map fun c => c.queryCount k).sum

/-- External elementary gates, plus linear work to measure the success wires.
The input black boxes' internal gates are charged separately. -/
def SparseFourierSolver.gates {N b w : ℕ} (S : SparseFourierSolver N b w) : ℕ :=
  (S.attempts.map OracleCircuit.gateCount).sum + S.attempts.length * S.successWires.card

/-- Embed the whole native SELECT register, including its scratch, in qubits. -/
def simulationEmbedding {N s q : ℕ} (G : CKSFourier.Grid)
    (e : ((G.Index × Fin N) × Qubits s) ↪ Qubits q) :
    Matrix (Qubits q) ((G.Index × Fin N) × Qubits s) ℂ :=
  Matrix.of fun z i => if z = e i then 1 else 0

/-- Concrete sparse SELECT implementation and capped solver, chosen before hidden inputs. -/
structure SparseImplementation (N b w s : ℕ) (G : CKSFourier.Grid) where
  simulationQubits : ℕ
  embedding : ((G.Index × Fin N) × Qubits s) ↪ Qubits simulationQubits
  simulation : OracleCircuit oneTwoQubitGateSet (fun k : Fin 2 =>
    if k = 0 then Nat.clog 2 N + Nat.clog 2 N else Nat.clog 2 N + Nat.clog 2 N + b)
    simulationQubits
  uncontrolled : ∀ step ∈ simulation, match step with
    | .gate _ => True
    | .query _ _ control _ _ => control = none
  solver : SparseFourierSolver N b w

/-- Fixed ordinary binary format, not an arbitrary numerical lookup-table decoder. -/
def sparseOracles {N w : ℕ} (F : LinearSystemAccess.BinaryComplexFormat)
    (PA : (k : Fin 2) → Matrix
      (Qubits (if k = 0 then Nat.clog 2 N + Nat.clog 2 N else Nat.clog 2 N + Nat.clog 2 N + F.width))
      (Qubits (if k = 0 then Nat.clog 2 N + Nat.clog 2 N else Nat.clog 2 N + Nat.clog 2 N + F.width)) ℂ)
    (PB : Matrix (Qubits (Nat.clog 2 N + w)) (Qubits (Nat.clog 2 N + w)) ℂ) :
    (k : Fin 3) → Matrix (Qubits (sparseWidths N F.width w k))
      (Qubits (sparseWidths N F.width w k)) ℂ :=
  Fin.cases (PA 0) (Fin.cases (PA 1) (fun k => by simpa [sparseWidths, Fin.eq_zero k] using PB))

/-- Theorem 3 (Fourier approach), CKS arXiv:1511.02306v2, PDF/printed p.4; Problem 1
and access promises pp.2–3; coherent SELECT pp.7–8,12; gate calculation p.15.
Both nonsparse reduction and sparse specialization are asserted. Constants precede all
varying parameters; algorithms precede hidden inputs. Approximation and amplification are
conclusions. The p.15 typo tau = y_J y_K is read as y_J z_K, as in (18),(31),(52).
The p.8 printed "upper bound on the probability q" is read as a positive lower bound,
as required by the inverse-square-root cost and the worst-case cap in Corollary 10.
P_B acts on the state register, as in pp.2–3,8. An arbitrary extra preparation register
would require extra gates for the zero-state reflection, which (54) does not budget.
The namespace follows this unit's explicit module contract. -/
theorem fourier_qlsp :
    ∃ Ccalls Ctime Cprecision Cqueries Cgates : ℝ,
      0 < Ccalls ∧ 0 < Ctime ∧ 0 < Cprecision ∧ 0 < Cqueries ∧ 0 < Cgates ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
    ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ (N : ℕ) (hN : 0 < N) (kappa eps : ℝ), 1 ≤ kappa → 0 < eps → eps ≤ eps0 →
      threshold ≤ kappa / eps →
    ∀ (prepBound : Polynomial ℕ),
    let w : ℕ := 0
    ∃ G : CKSFourier.Grid,
      (∀ j k, |G.y j * G.z k| ≤ Ctime * kappa * precisionLog kappa eps) ∧
    ∃ reductions : (s : ℕ) → FourierReduction N w s G,
      (∀ s, ∀ (A : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A) (hpromise : MatrixPromise A kappa),
        ∀ (bvec : EuclideanSpace ℂ (Fin N)) (hb : bvec ≠ 0),
        ∀ PB : Matrix (Qubits (Nat.clog 2 N + w)) (Qubits (Nat.clog 2 N + w)) ℂ,
          LinearSystemAccess.IsWorkspaceStatePrep bvec PB →
          (∃ c : Circuit oneTwoQubitGateSet (Nat.clog 2 N + w),
            c.unitary = PB ∧ c.size ≤ prepBound.eval (Nat.clog 2 N)) →
        ∀ V : Matrix ((G.Index × Fin N) × Qubits s) ((G.Index × Fin N) × Qubits s) ℂ,
          CKSFourier.IsCoherentSelectSimulation G A hpromise.1 s V
            (Cprecision * eps / (kappa * Real.sqrt (precisionLog kappa eps))) →
          let R := reductions s
          let O := reductionOracles V PB
          PureFlaggedOutput hN A hA bvec hb
            (normalizedVec (act (simulatedInverse G V) (normalizedVec bvec)))
            (RetainedOracle.retainedOutput R.layout R.program O (pureDensity R.start) true)
            (RetainedOracle.retainedOutput R.layout R.program O (pureDensity R.start) false) eps ∧
          ∀ k : Fin 2,
            (RetainedOracle.worstCaseQueries R.program O (fun j => if j = k then 1 else 0)
              (pureDensity R.start) : ℝ) ≤ Ccalls * kappa * Real.sqrt (precisionLog kappa eps)) ∧
      (∀ (d : ℕ), 1 ≤ d → d ≤ N → ∀ F : LinearSystemAccess.BinaryComplexFormat,
        ∃ s : ℕ, ∃ S : SparseImplementation N F.width w s G,
        ∀ (A : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A) (hpromise : MatrixPromise A kappa), IsSparse A d →
        ∀ (bvec : EuclideanSpace ℂ (Fin N)) (hb : bvec ≠ 0),
        ∀ PA : (k : Fin 2) → Matrix
          (Qubits (if k = 0 then Nat.clog 2 N + Nat.clog 2 N else Nat.clog 2 N + Nat.clog 2 N + F.width))
          (Qubits (if k = 0 then Nat.clog 2 N + Nat.clog 2 N else Nat.clog 2 N + Nat.clog 2 N + F.width)) ℂ,
          IsSparseAccessOracle A d F.decode (PA 0) (PA 1) →
        ∀ PB : Matrix (Qubits (Nat.clog 2 N + w)) (Qubits (Nat.clog 2 N + w)) ℂ,
          LinearSystemAccess.IsWorkspaceStatePrep bvec PB →
          (∃ c : Circuit oneTwoQubitGateSet (Nat.clog 2 N + w),
            c.unitary = PB ∧ c.size ≤ prepBound.eval (Nat.clog 2 N)) →
          let J := simulationEmbedding G S.embedding
          let V := Jᴴ * S.simulation.unitary PA * J
          let O := sparseOracles F PA PB
          let R := reductions s
          CKSFourier.IsCoherentSelectSimulation G A hpromise.1 s V
            (Cprecision * eps / (kappa * Real.sqrt (precisionLog kappa eps))) ∧
          S.simulation.unitary PA * J = J * V ∧
          S.solver.output O =
            RetainedOracle.retainedOutput R.layout R.program (reductionOracles V PB)
              (pureDensity R.start) true ∧
          (S.solver.successState O S.solver.attempts).trace.re = (S.solver.output O).trace.re ∧
          PureFlaggedOutput hN A hA bvec hb
            (normalizedVec (act (simulatedInverse G V) (normalizedVec bvec)))
            (S.solver.output O)
            (RetainedOracle.retainedOutput R.layout R.program (reductionOracles V PB)
              (pureDensity R.start) false) eps ∧
          (S.solver.queries 0 + S.solver.queries 1 : ℝ) ≤
            Cqueries * d * kappa ^ 2 * (precisionLog kappa eps) ^ (5 / 2 : ℝ) ∧
          (S.solver.queries 2 : ℝ) ≤ Ccalls * kappa * Real.sqrt (precisionLog kappa eps) ∧
          (S.solver.gates : ℝ) ≤ Cgates * d * kappa ^ 2 *
            (precisionLog kappa eps) ^ (5 / 2 : ℝ) *
              (Real.log N + (precisionLog kappa eps) ^ (5 / 2 : ℝ))) := by sorry

end QAlgorithms.Papers.RoadmapA10

