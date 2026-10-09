import QAlgorithms.Defs.Gates

/-!
# Quantum circuits over a gate set (shared definition layer)

A gate is a matrix on `k` qubits; a circuit on `n` wires is a list of gates from a gate set,
each placed on an ordered tuple of distinct wires, applied in list order (head first). Its size
is the number of gates. Oracle circuits add black-box calls, so that statements counting both
queries and other gates can be stated (de Wolf §2.4, the CKS cost model).
-/

namespace QAlgorithms

/-- de Wolf p.26 (§2.1.2), p.121 (§13.1); Childs p.9 (§1.2): an elementary gate, a matrix acting
on `arity` qubits (wire `a` of the gate is the `a`-th tensor factor, most significant first).
A gate set is a `Set Gate`. Unitarity is the separate predicate `Gate.IsUnitary`, because a gate
set's being unitary is a hypothesis of the source's statements. -/
structure Gate where
  /-- The number of qubits the gate acts on. -/
  arity : ℕ
  /-- The gate's matrix on `arity` qubits. -/
  mat : Matrix (Qubits arity) (Qubits arity) ℂ

/-- de Wolf p.26 (§2.1.2): a quantum gate is a unitary transformation. -/
def Gate.IsUnitary (g : Gate) : Prop :=
  g.mat ∈ Matrix.unitaryGroup (Qubits g.arity) ℂ

/-- A single-qubit matrix (indexed by `Bool`) as an arity-1 gate. -/
def Gate.ofMatrix1 (M : Matrix Bool Bool ℂ) : Gate :=
  ⟨1, M.submatrix (fun b => b 0) (fun b => b 0)⟩

/-- A two-qubit matrix (indexed by `Bool × Bool`) as an arity-2 gate; gate wire `0` is the first
factor (the control of `cnot` and of a `controlled` gate). -/
def Gate.ofMatrix2 (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Gate :=
  ⟨2, M.submatrix (fun b => (b 0, b 1)) (fun b => (b 0, b 1))⟩

/-- Childs p.9 (§1.2), de Wolf p.26 (§2.1.2), p.129 (§14.2, Definition 2): the operator `M` on
`k` qubits applied to the ordered tuple of distinct wires `w` of an `n`-qubit register, tensored
with the identity on the other wires (gate wire `a` is register wire `w a`). Its `(y, z)` entry is
`M (y ∘ w) (z ∘ w)` when `y` and `z` agree off the range of `w`, and `0` otherwise. -/
def embedOp {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z =>
    if ∀ a : Fin n, a ∉ Set.range w → y a = z a then M (y ∘ w) (z ∘ w) else 0

/-- de Wolf p.26, Childs p.9: one gate of a circuit over the gate set `S` on `n` wires: a gate of
`S` and the distinct wires it acts on. -/
structure GateApp (S : Set Gate) (n : ℕ) where
  /-- The gate. -/
  gate : Gate
  /-- It belongs to the gate set. -/
  mem : gate ∈ S
  /-- The register wires it acts on, in the order of the gate's own wires. -/
  wires : Fin gate.arity ↪ Fin n

/-- de Wolf p.26 (§2.1.2), p.121 (§13.1); Childs p.9 (§1.2), p.10 (§1.3): a quantum circuit on
`n` wires over the gate set `S`, a list of gate applications performed in list order (head
first). -/
abbrev Circuit (S : Set Gate) (n : ℕ) := List (GateApp S n)

/-- The unitary `U_t ⋯ U_2 U_1` implemented by the circuit `[U_1, …, U_t]` (the first gate is the
rightmost factor; the empty circuit implements the identity). -/
def Circuit.unitary {S : Set Gate} {n : ℕ} (c : Circuit S n) : Matrix (Qubits n) (Qubits n) ℂ :=
  (c.map fun g => embedOp g.gate.mat g.wires).reverse.prod

/-- de Wolf p.25–26, Childs p.9: the size of a circuit, its number of elementary gates. -/
def Circuit.size {S : Set Gate} {n : ℕ} (c : Circuit S n) : ℕ :=
  c.length

/-- de Wolf p.121 (§13.1): the initial state `|x, 0^w⟩`: the input `x` on wires `0, …, n-1`
followed by `w` workspace qubits in `|0⟩`. -/
noncomputable def inputState {n : ℕ} (x : Qubits n) (w : ℕ) : EuclideanSpace ℂ (Qubits (n + w)) :=
  ket (Fin.append x (fun _ : Fin w => false))

/-- de Wolf p.121 (§13.1): the circuit `c` on `n + w` wires computes `f : {0,1}ⁿ → {0,1}` if for
every input `x`, measuring the output wire `out` of the final state `C|x, 0^w⟩` gives `f(x)` with
probability at least `2/3` (worst case over `x`). De Wolf's "first qubit" is `out = 0`. -/
def Circuit.ComputesBool {S : Set Gate} {n w : ℕ} (c : Circuit S (n + w)) (out : Fin (n + w))
    (f : Qubits n → Bool) : Prop :=
  ∀ x : Qubits n, probEvent (act c.unitary (inputState x w)) (fun z => z out = f x) ≥ 2 / 3

/-- Childs p.10 (§1.3, (1.3)–(1.4)) with p.16 (§2.2: "a global phase is irrelevant"): `V`
approximates `U` to precision `ε` in the spectral norm up to a global phase,
`∃ θ, ‖U − e^{iθ} V‖ ≤ ε`. The phase is allowed because the source's own universal set
`{H, T, C}` generates only circuits of determinant `1` on three or more qubits, so it could not
be universal under the phase-sensitive reading of (1.3). -/
def ApproxUpToPhase {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : Matrix ι ι ℂ) (ε : ℝ) : Prop :=
  ∃ θ : ℝ, specNorm (U - Complex.exp (θ * Complex.I) • V) ≤ ε

/-- Childs p.10 (§1.3): a gate set is universal if every unitary on any fixed number `k` of qubits
can be approximated to any precision `δ > 0` by a circuit over the set on those `k` qubits
(no ancillas), up to a global phase (`ApproxUpToPhase`). That every gate is a unitary on one or
two qubits (Childs's setting) is a hypothesis of the statements, not part of this predicate. -/
def IsUniversal (S : Set Gate) : Prop :=
  ∀ (k : ℕ) (U : Matrix (Qubits k) (Qubits k) ℂ), U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
    ∀ δ : ℝ, 0 < δ → ∃ c : Circuit S k, ApproxUpToPhase U c.unitary δ

/-- Childs p.15 (Theorem 2.1): a gate set is closed under inverses: with every gate `U` it contains
`U† = U⁻¹` (on the same number of qubits). -/
def ClosedUnderInverse (S : Set Gate) : Prop :=
  ∀ g ∈ S, (⟨g.arity, star g.mat⟩ : Gate) ∈ S

/-- Childs p.16 (§2.2, (2.8)): the ball `S_ε = {U ∈ SU(2) : ‖I − U‖ ≤ ε}` around the identity. -/
def su2Ball (ε : ℝ) : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  {U | specNorm (1 - (U : Matrix (Fin 2) (Fin 2) ℂ)) ≤ ε}

/-- Childs p.16 (§2.2): `Γ` is an `ε`-net for `S` (both subsets of `SU(2)`) if every `A ∈ S` has
some `U ∈ Γ` with `‖A − U‖ ≤ ε`. -/
def IsNet (Γ S : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) : Prop :=
  ∀ A ∈ S, ∃ U ∈ Γ, specNorm ((A : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)) ≤ ε

/-- Childs p.16 (§2.2, (2.7)): `⟦Γ, Γ⟧ = {⟦U, V⟧ : U, V ∈ Γ}` with the group commutator
`⟦U, V⟧ = U V U⁻¹ V⁻¹`. -/
def commutatorSet (Γ : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Set (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  {W | ∃ U ∈ Γ, ∃ V ∈ Γ, W = U * V * U⁻¹ * V⁻¹}

/-! ### Circuits with oracle calls -/

/-- One step of an oracle circuit over the gate set `S` on `n` wires, with `r` black boxes of
arities `a k`: either a gate of `S`, or a call to oracle `k` (its inverse if `adjoint`), possibly
controlled on a wire `control` that is not among the call's wires. -/
inductive OracleStep (S : Set Gate) {r : ℕ} (a : Fin r → ℕ) (n : ℕ) where
  /-- An elementary gate. -/
  | gate (g : GateApp S n)
  /-- A call to oracle `k` on the distinct wires `wires`. -/
  | query (k : Fin r) (adjoint : Bool) (control : Option (Fin n)) (wires : Fin (a k) ↪ Fin n)
      (hc : ∀ c, control = some c → c ∉ Set.range wires)

/-- de Wolf p.29 (§2.4), p.30 (§2.4.1); Childs p.105 (§21.1); CKS2017 (cost model): a gate-level
circuit with black-box calls, applied in list order (head first). The gates do not depend on the
oracles: the oracles enter only through `OracleCircuit.unitary`'s argument (trap Q2). -/
abbrev OracleCircuit (S : Set Gate) {r : ℕ} (a : Fin r → ℕ) (n : ℕ) := List (OracleStep S a n)

/-- The controlled version of an operator on `m` qubits, as an operator on `m + 1` qubits whose
wire `0` is the control. -/
def controlledQubits {m : ℕ} (M : Matrix (Qubits m) (Qubits m) ℂ) :
    Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  (controlled M).submatrix (fun y => (y 0, Fin.tail y)) (fun y => (y 0, Fin.tail y))

/-- The matrix of one oracle-circuit step on the whole register, given the oracles `orc`. -/
def OracleStep.mat {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleStep S a n → Matrix (Qubits n) (Qubits n) ℂ
  | .gate g => embedOp g.gate.mat g.wires
  | .query k adj none wires _ => embedOp (if adj then star (orc k) else orc k) wires
  | .query k adj (some c) wires hc =>
      embedOp (controlledQubits (if adj then star (orc k) else orc k))
        ⟨Fin.cons c wires, Fin.cons_injective_iff.2 ⟨hc c rfl, wires.injective⟩⟩

/-- The unitary implemented by an oracle circuit with the oracles `orc` (first step rightmost). -/
def OracleCircuit.unitary {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (c.map (OracleStep.mat orc)).reverse.prod

/-- Whether a step is a call to oracle `k` (plain, inverse or controlled). -/
def OracleStep.IsQueryTo {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} (k : Fin r) :
    OracleStep S a n → Bool
  | .gate _ => false
  | .query k' _ _ _ _ => decide (k' = k)

/-- The number of calls to oracle `k` in any variant (plain, inverse, controlled): the query
count of de Wolf §2.4 and of CKS2017. -/
def OracleCircuit.queryCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) (k : Fin r) : ℕ :=
  c.countP (OracleStep.IsQueryTo k)

/-- The number of elementary-gate steps ("other operations", CKS's gate complexity). -/
def OracleCircuit.gateCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) : ℕ :=
  c.countP fun s => match s with
    | .gate _ => true
    | .query _ _ _ _ _ => false

/-! ### Sanity tests -/

theorem embedOp_one {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; apply hyz; funext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨b, rfl⟩ := ha; exact congrFun h2 b
      · exact h1 a ha
    · rfl
    · rfl

example : Circuit.unitary ([] : Circuit ∅ 3) = 1 := rfl

/-- Embedding a gate on the single wire of a one-qubit register gives the gate itself. -/
example (y z : Qubits 1) :
    embedOp (hadamard.submatrix (fun b : Qubits 1 => b 0) (fun b => b 0))
      (Function.Embedding.refl (Fin 1)) y z = hadamard (y 0) (z 0) := by
  unfold embedOp
  rw [Matrix.of_apply, if_pos (fun a ha => absurd ⟨a, rfl⟩ ha)]
  rfl

example {S : Set Gate} {n : ℕ} (g h : GateApp S n) :
    Circuit.unitary [g, h] = embedOp h.gate.mat h.wires * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

/-- A circuit without oracle calls does not depend on the oracles. -/
example {S : Set Gate} {n : ℕ} (g : GateApp S n)
    (orc orc' : (k : Fin 1) → Matrix (Qubits ((fun _ => 1) k)) (Qubits ((fun _ => 1) k)) ℂ) :
    OracleCircuit.unitary [OracleStep.gate g] orc = OracleCircuit.unitary [OracleStep.gate g] orc' :=
  rfl

end QAlgorithms
