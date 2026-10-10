import QAlgorithms.Defs.BinaryStabilizer

/-!
# Circuits of locations: preparation, gates, measurement, wait; faults and output distributions
(shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages), §4.1 and Def. 6.

Model. A circuit on `N` qubits (wires `Fin N`) is a list of time steps, each a list of locations
(§4.1, p.17): preparation of `|0⟩`, the gates `H`, `R_{π/8} = diag(1, e^{iπ/4})` (frozen `gateT`)
and CNOT, standard-basis measurement, and wait. A location is identified by `(s, j) : ℕ × ℕ`
(time step `s`, position `j` in the step). The measurement record lists the outcomes in
step-major order. Gate locations may be classically controlled by earlier outcomes (classical
computation is perfect and free, p.17); the condition reads the outcomes by location id and sees
only the outcomes of earlier time steps. The state of the computer is classical–quantum: for each
measurement record, a subnormalized density matrix on the qubits and an environment register `E`
(trivial, `Fin 1`, when no environment is needed). An error assignment puts a superoperator on
qubits ⊗ environment at some locations: after the location's ideal action, and before it for a
measurement location.
-/

namespace QAlgorithms

open scoped Matrix

/-- Gottesman intro p.17 (§4.1) and p.33 (Def. 6): the types of location: preparation of `|0⟩`,
the gates `H`, `R_{π/8}`, CNOT (the universal set of p.17), measurement in the standard basis, and
wait. -/
inductive LocKind where
  | prep
  | had
  | tgate
  | cnot
  | meas
  | wait
  deriving DecidableEq

/-- Gottesman intro p.18: the number of qubits a location involves (two for CNOT, one
otherwise). -/
def LocKind.arity : LocKind → ℕ
  | .cnot => 2
  | _ => 1

theorem LocKind.arity_pos (κ : LocKind) : 0 < κ.arity := by
  cases κ <;> decide

/-- Gottesman intro p.17 (§4.1): the gate locations `H`, `R_{π/8}`, CNOT (classical control is
meaningful for these only). -/
def LocKind.IsGate : LocKind → Bool
  | .had => true
  | .tgate => true
  | .cnot => true
  | _ => false

/-- Gottesman intro p.17 (§4.1): the ideal unitary of a location on its qubits: `H` (frozen
`hadamard`), `R_{π/8} = diag(1, e^{iπ/4})` (frozen `gateT`), CNOT (frozen `cnot`, control on the
first wire), and the identity for wait (and, unused, for preparation and measurement). -/
noncomputable def LocKind.idealMatrix : (κ : LocKind) → Matrix (Qubits κ.arity) (Qubits κ.arity) ℂ
  | .had => (Gate.ofMatrix1 hadamard).mat
  | .tgate => (Gate.ofMatrix1 gateT).mat
  | .cnot => (Gate.ofMatrix2 QAlgorithms.cnot).mat
  | .prep => 1
  | .meas => 1
  | .wait => 1

/-- Gottesman intro p.17 (§4.1): a location on `N` qubits: its type, the qubits it acts on (in
order: control first for CNOT), and, for gate locations, a classical condition on the earlier
measurement outcomes (given by location id; `none` for an outcome not available). The gate is
applied iff the condition holds; the location exists, and can be faulty, either way. The
condition is ignored for preparation, measurement and wait locations. -/
structure Loc (N : ℕ) where
  kind : LocKind
  wires : Fin kind.arity ↪ Fin N
  cond : (ℕ × ℕ → Option Bool) → Bool

/-- The set of qubits a location acts on. -/
def Loc.qubits {N : ℕ} (l : Loc N) : Finset (Fin N) :=
  Finset.univ.map l.wires

/-- Gottesman intro p.17 (§4.1) and p.33 (Def. 6): a circuit of locations on `N` qubits, organised
in time steps. -/
structure LocCircuit (N : ℕ) where
  steps : List (List (Loc N))

namespace LocCircuit

variable {N : ℕ}

/-- The location with id `(s, j)` (time step `s`, position `j`), if any. -/
def locAt (C : LocCircuit N) (ℓ : ℕ × ℕ) : Option (Loc N) :=
  (C.steps.getD ℓ.1 [])[ℓ.2]?

/-- Gottesman intro p.17: the set of (ids of) locations of the circuit. -/
def locs (C : LocCircuit N) : Finset (ℕ × ℕ) :=
  (Finset.range C.steps.length).biUnion fun s =>
    (Finset.range (C.steps.getD s []).length).image fun j => (s, j)

/-- The number of qubits of the circuit. -/
def numQubits (_ : LocCircuit N) : ℕ :=
  N

/-- The number of time steps of the circuit. -/
def numSteps (C : LocCircuit N) : ℕ :=
  C.steps.length

/-- Gottesman intro p.41 (Thm 10): `|C|`, the number of locations. -/
def size (C : LocCircuit N) : ℕ :=
  C.locs.card

/-- The ids of the measurement locations, in the order of the measurement record (step-major,
then by position). -/
def measIds (C : LocCircuit N) : List (ℕ × ℕ) :=
  C.steps.zipIdx.flatMap fun p =>
    p.1.zipIdx.filterMap fun q => if q.1.kind = .meas then some (p.2, q.2) else none

/-- The number of measurement locations, i.e. the length of the measurement record. -/
def measCount (C : LocCircuit N) : ℕ :=
  C.measIds.length

/-- The outcome recorded in `r` at the measurement location `ℓ` (`none` if `ℓ` is not a
measurement location or `r` is too short). -/
def outcomeAt (C : LocCircuit N) (r : List Bool) (ℓ : ℕ × ℕ) : Option Bool :=
  (C.measIds.zip r).lookup ℓ

end LocCircuit

/-- The qubits acted on by a list of locations. -/
def qubitsOf {N : ℕ} (ls : List (Loc N)) : Finset (Fin N) :=
  ls.foldr (fun l acc => l.qubits ∪ acc) ∅

/-- Gottesman intro p.33 (Def. 6: "the preparation locations introduce new qubits into the
circuit, and the measurement locations remove qubits"): the live qubits after a time step. -/
def stepLive {N : ℕ} (live : Finset (Fin N)) (st : List (Loc N)) : Finset (Fin N) :=
  (live ∪ qubitsOf (st.filter fun l => decide (l.kind = .prep))) \
    qubitsOf (st.filter fun l => decide (l.kind = .meas))

namespace LocCircuit

variable {N : ℕ}

/-- The live qubits at the start of time step `s`, starting from the live set `liveIn`. -/
def liveBefore (C : LocCircuit N) (liveIn : Finset (Fin N)) : ℕ → Finset (Fin N)
  | 0 => liveIn
  | s + 1 => stepLive (C.liveBefore liveIn s) (C.steps.getD s [])

/-- Gottesman intro p.33 (Def. 6), relative to boundary live sets: within each time step the
locations act on pairwise disjoint qubits; every live qubit ("not counting those to be added at
later time steps or removed at earlier time steps") is involved in a location of the step (hence
in exactly one); a preparation acts only on a qubit that is not live and every other location only
on live qubits; and the live qubits after the last step are `liveOut`. A full circuit has
`liveIn = liveOut = ∅` (the first location of every qubit is a preparation and the last a
measurement); a gadget has the data qubits of its input and output blocks. -/
def IsWellFormed (C : LocCircuit N) (liveIn liveOut : Finset (Fin N)) : Prop :=
  (∀ s < C.steps.length,
    (C.steps.getD s []).Pairwise (fun l l' => Disjoint l.qubits l'.qubits) ∧
    (∀ q ∈ C.liveBefore liveIn s, ∃ l ∈ C.steps.getD s [], q ∈ l.qubits) ∧
    (∀ l ∈ C.steps.getD s [], l.kind = .prep → Disjoint l.qubits (C.liveBefore liveIn s)) ∧
    (∀ l ∈ C.steps.getD s [], l.kind ≠ .prep → l.qubits ⊆ C.liveBefore liveIn s)) ∧
  C.liveBefore liveIn C.steps.length = liveOut

/-- Gottesman intro p.19 ("the original circuit takes no input: all qubits used in it must be
prepared using preparation locations"; its output is the outcome of the final measurements) and
p.33 (Def. 6): an ideal circuit: well formed with empty boundaries, and without classical
control. -/
def IsIdealCircuit (C : LocCircuit N) : Prop :=
  C.IsWellFormed ∅ ∅ ∧ ∀ st ∈ C.steps, ∀ l ∈ st, l.cond = fun _ => true

end LocCircuit

/-- Gottesman intro p.18 (§4.1) and p.40 (Def. 12): an error assignment for a circuit on `N`
qubits with environment `E`: `some Φ` at a location applies the superoperator `Φ` (on qubits ⊗
environment) right after the location's ideal operation (right before it, for a measurement):
"the actual error should be considered to be the action of the failed component times the inverse
of the desired component". -/
abbrev ErrAssign (N : ℕ) (E : Type*) :=
  ℕ × ℕ → Option (Superop (Qubits N × E) (Qubits N × E))

/-- A classical–quantum state: for each measurement record, a subnormalized density matrix on
qubits ⊗ environment. -/
abbrev CQState (N : ℕ) (E : Type*) :=
  List Bool → Matrix (Qubits N × E) (Qubits N × E) ℂ

/-- The single-qubit operator `M` on wire `q` (identity elsewhere). -/
def qubitOp1 {N : ℕ} (M : Matrix Bool Bool ℂ) (q : Fin N) : Matrix (Qubits N) (Qubits N) ℂ :=
  embedOp (Gate.ofMatrix1 M).mat (Stabilizer.wire1 q)

/-- The reset Kraus operators `|0⟩⟨b|` (a preparation location resets its qubit to `|0⟩`). -/
def resetKraus (b : Bool) : Matrix Bool Bool ℂ :=
  Matrix.of fun y z => if y = false ∧ z = b then 1 else 0

/-- The standard-basis projectors `|b⟩⟨b|` (p.17: measurement of individual qubits in the
standard basis). -/
def measProj (b : Bool) : Matrix Bool Bool ℂ :=
  Matrix.of fun y z => if y = b ∧ z = b then 1 else 0

/-- Gottesman intro pp.17–18: the action of one location on a classical–quantum state, with the
condition reading the outcomes through `O` and with the assigned error `e`. Preparation: reset
the qubit to `|0⟩`, then the error. Gate: the ideal unitary on its qubits if the condition holds
(identity otherwise), then the error. Wait: the error only. Measurement: the error, then the
branch of record `r ++ [b]` receives `Π_b ρ_r Π_b`. -/
noncomputable def Loc.apply {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E] (l : Loc N)
    (O : List Bool → ℕ × ℕ → Option Bool) (e : Option (Superop (Qubits N × E) (Qubits N × E)))
    (ρ : CQState N E) : CQState N E :=
  let errF : Matrix (Qubits N × E) (Qubits N × E) ℂ → Matrix (Qubits N × E) (Qubits N × E) ℂ :=
    fun X => match e with
      | none => X
      | some Φ => Φ X
  let q : Fin N := l.wires ⟨0, l.kind.arity_pos⟩
  let lift : Matrix (Qubits N) (Qubits N) ℂ → Matrix (Qubits N × E) (Qubits N × E) ℂ :=
    fun M => Matrix.kronecker M 1
  match l.kind with
  | .prep => fun r => errF (krausApply (fun b : Bool => lift (qubitOp1 (resetKraus b) q)) (ρ r))
  | .meas => fun r => match r.getLast? with
      | none => 0
      | some b => conjSuperop (lift (qubitOp1 (measProj b) q)) (errF (ρ r.dropLast))
  | .wait => fun r => errF (ρ r)
  | .had | .tgate | .cnot => fun r => errF (if l.cond (O r) then
      conjSuperop (lift (embedOp l.kind.idealMatrix l.wires)) (ρ r) else ρ r)

/-- The locations of one time step `s`, applied in list order (position `j` upward). -/
noncomputable def runStep {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (O : List Bool → ℕ × ℕ → Option Bool) (err : ErrAssign N E) (s : ℕ) :
    List (Loc N) → ℕ → CQState N E → CQState N E
  | [], _, ρ => ρ
  | l :: ls, j, ρ => runStep O err s ls (j + 1) (l.apply O (err (s, j)) ρ)

namespace LocCircuit

variable {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- The time steps `s, s + 1, …` given by the list, in order; at step `s` the conditions see the
outcomes of the measurement locations of steps `< s`. -/
noncomputable def runFrom (C : LocCircuit N) (err : ErrAssign N E) :
    List (List (Loc N)) → ℕ → CQState N E → CQState N E
  | [], _, ρ => ρ
  | st :: rest, s, ρ =>
      C.runFrom err rest (s + 1)
        (runStep (fun r ℓ => if ℓ.1 < s then C.outcomeAt r ℓ else none) err s st 0 ρ)

/-- Gottesman intro pp.17–18: the classical–quantum state after running the whole circuit with the
error assignment `err` from the state `ρ`. -/
noncomputable def run (C : LocCircuit N) (err : ErrAssign N E) (ρ : CQState N E) : CQState N E :=
  C.runFrom err C.steps 0 ρ

end LocCircuit

/-- The initial state: all qubits `|0⟩` (immaterial for circuits that prepare every qubit before
use), the environment in `σ0`, the empty record. -/
noncomputable def initState (N : ℕ) {E : Type*} (σ0 : Matrix E E ℂ) : CQState N E :=
  fun r => if r = [] then Matrix.kronecker (pureDensity (zeroKet N)) σ0 else 0

namespace LocCircuit

variable {N : ℕ}

/-- Gottesman intro p.19 and p.36 (Thm 7): the output distribution of the circuit: the
probability of each measurement record (outcomes in step-major order) under the error assignment
`err`, the environment starting in `σ0`. -/
noncomputable def outDist {E : Type*} [Fintype E] [DecidableEq E] (C : LocCircuit N)
    (err : ErrAssign N E) (σ0 : Matrix E E ℂ) : (Fin C.measCount → Bool) → ℝ :=
  fun r => (C.run err (initState N σ0) (List.ofFn r)).trace.re

/-- Gottesman intro p.19: the output distribution of the circuit without errors. -/
noncomputable def idealOutDist (C : LocCircuit N) : (Fin C.measCount → Bool) → ℝ :=
  C.outDist (E := Fin 1) (fun _ => none) 1

end LocCircuit

/-- Gottesman intro p.19 ("the final fault-tolerant measurement gadgets will produce classical
information which should … give the same outcome as the original circuit"): the distribution of
the classically decoded record `dec r′` when `r′` has distribution `μ`. -/
def pushDist {M M' : ℕ} (dec : List Bool → List Bool) (μ : (Fin M' → Bool) → ℝ) :
    (Fin M → Bool) → ℝ :=
  fun r => ∑ r' ∈ Finset.univ.filter (fun r' : Fin M' → Bool => dec (List.ofFn r') = List.ofFn r), μ r'

/-- Gottesman intro p.20 ("restrict attention to cases where the error associated to each fault is
a Pauli operator"): a Pauli fault arrangement: `some (P, Q)` makes the location faulty with the
Pauli error `P` on its first qubit and `Q` on its second (`Q` is ignored for one-qubit
locations). -/
abbrev PauliArrangement :=
  ℕ × ℕ → Option (Stabilizer.Pauli × Stabilizer.Pauli)

/-- The faulty locations of the circuit under a Pauli arrangement (p.20: the `s` of a gadget is
their number). -/
def faultyLocs {N : ℕ} (C : LocCircuit N) (fa : PauliArrangement) : Finset (ℕ × ℕ) :=
  C.locs.filter fun ℓ => fa ℓ ≠ none

/-- The Pauli operator `P` (first qubit) `⊗ Q` (other qubits) on the qubits of a location. -/
noncomputable def locPauli (k : ℕ) (P Q : Stabilizer.Pauli) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun y z => ∏ i : Fin k, (if (i : ℕ) = 0 then P else Q).mat (y i) (z i)

/-- Gottesman intro p.20: the error assignment of a Pauli arrangement: conjugation by the Pauli
error on the qubits of each faulty location (trivial environment). -/
noncomputable def pauliErr {N : ℕ} (C : LocCircuit N) (fa : PauliArrangement) :
    ErrAssign N (Fin 1) :=
  fun ℓ => match C.locAt ℓ, fa ℓ with
    | some l, some pq =>
        some (conjSuperop (Matrix.kronecker (embedOp (locPauli l.kind.arity pq.1 pq.2) l.wires)
          (1 : Matrix (Fin 1) (Fin 1) ℂ)))
    | _, _ => none

/-- Gottesman intro p.18 ("an error that can affect all of the qubits involved in the action") and
p.40 (Def. 12: "any quantum operation"): `Φ` is an admissible error at a location with qubits `w`:
some quantum operation on those qubits jointly with the environment, the identity on the other
qubits. -/
def IsLocError {N k : ℕ} (w : Fin k ↪ Fin N) {E : Type*} [Fintype E] [DecidableEq E]
    (Φ : Superop (Qubits N × E) (Qubits N × E)) : Prop :=
  ∃ Ψ : Superop ((Fin k → Bool) × E) ((Fin k → Bool) × E), IsChannel Ψ ∧ Φ = liftSuperop w Ψ

/-! ### Sanity tests -/

example : LocKind.cnot.arity = 2 ∧ LocKind.meas.arity = 1 := ⟨rfl, rfl⟩

example (y z : Qubits 1) : LocKind.had.idealMatrix y z = hadamard (y 0) (z 0) := rfl

example {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E] (err : ErrAssign N E) (ρ : CQState N E) :
    (⟨[]⟩ : LocCircuit N).run err ρ = ρ := rfl

example {N : ℕ} : (⟨[]⟩ : LocCircuit N).IsWellFormed ∅ ∅ :=
  ⟨fun s hs => absurd hs (by simp), rfl⟩

example : (⟨[[⟨.prep, Stabilizer.wire1 0, fun _ => true⟩], [⟨.meas, Stabilizer.wire1 0, fun _ => true⟩]]⟩ :
    LocCircuit 1).measIds = [(1, 0)] := rfl

example {M : ℕ} (μ : (Fin M → Bool) → ℝ) : pushDist id μ = μ := by
  funext r
  simp [pushDist, List.ofFn_inj, Finset.filter_eq']

example {N : ℕ} (C : LocCircuit N) : faultyLocs C (fun _ => none) = ∅ := by
  simp [faultyLocs]

example {N : ℕ} (C : LocCircuit N) (ℓ : ℕ × ℕ) : pauliErr C (fun _ => none) ℓ = none := by
  simp only [pauliErr]
  split <;> simp_all

end QAlgorithms
