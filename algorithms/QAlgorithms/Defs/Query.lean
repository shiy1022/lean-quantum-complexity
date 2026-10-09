import QAlgorithms.Defs.Classical

/-!
# Query oracles and query algorithms (shared definition layer)

Three oracle forms the sources distinguish (trap Q3): the standard (XOR) query
`|i, b⟩ ↦ |i, b ⊕ x_i⟩`, de Wolf's uncontrolled phase query `|i⟩ ↦ (−1)^{x_i} |i⟩`, and Childs's
controlled phase query `|i, b⟩ ↦ (−1)^{b x_i} |i, b⟩`. A `T`-query algorithm is
`U_T O U_{T−1} ⋯ U_1 O U_0` on a fixed start state, with input-independent unitaries.
-/

namespace QAlgorithms

/-- de Wolf p.29 (§2.4, "Ox : |i, b⟩ ↦ |i, b ⊕ x_i⟩"), p.35 (§3.1), p.51 (§5.3), p.60 (§6.2.2);
Childs p.106 ((21.2), (21.4)), p.133 (§26.1): the standard query to `f : ι → κ`, the permutation
matrix of `(i, y) ↦ (i, y + f i)`. With `κ = Bool` (`+` is xor) this is `O_x |i, b⟩ = |i, b ⊕ x_i⟩`;
with `κ = Fin m → Bool` it is the string query `|i, y⟩ ↦ |i, y ⊕ x_i⟩` (Simon, Shor's `O_f`, the
random-oracle query of Childs §26); with `κ = ZMod d` it is Childs's (21.4). -/
def xorOracle {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup κ] (f : ι → κ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = q.2 + f q.1 then 1 else 0

/-- de Wolf p.30 (§2.4: "`O_{x,±}`"), p.65 (§7.2): the (uncontrolled) phase query
`O_{x,±} |i⟩ = (−1)^{x_i} |i⟩`, with no target qubit. -/
def phaseOracle {ι : Type*} [DecidableEq ι] (x : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if x i then -1 else 1

/-- Childs p.106 ((21.3)): the controlled phase query `O_x |i, b⟩ = (−1)^{b x_i} |i, b⟩`. It equals
`(I ⊗ H) Ô_x (I ⊗ H)` for the XOR query `Ô_x`, but is kept separate because each statement must
use its source's oracle (trap Q3). -/
def controlledPhaseOracle {ι : Type*} [DecidableEq ι] (x : ι → Bool) :
    Matrix (ι × Bool) (ι × Bool) ℂ :=
  Matrix.diagonal fun p => if p.2 && x p.1 then -1 else 1

/-- de Wolf p.29 (§2.4), p.111 (§12.1: "`A = U_T O_x U_{T−1} ⋯ U_1 O_x U_0`, with initial state
`|0^m⟩`"); Childs p.105 (§21.1: "begins from a state that does not depend on the oracle string"),
p.106 ((21.1)), p.134 (§26.2): a `T`-query algorithm with query register `ι × κ` and workspace `W`.
The start state and the unitaries `U_0, …, U_T` are fields, fixed before any input (trap Q2); the
oracle is an argument of `stateAt`, applied as `O ⊗ I_W` between consecutive unitaries, so the
number of queries is exactly `T` (trap Q6). (De Wolf's start `|0^m⟩` with `U_0`, and Childs's
input-independent start `ψ` with `U_1, …, U_t`, give the same class.) -/
structure QueryAlg (ι κ W : Type*) [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq W] (T : ℕ) where
  /-- The input-independent initial state. -/
  start : EuclideanSpace ℂ ((ι × κ) × W)
  /-- It is a unit vector. -/
  start_unit : ‖start‖ = 1
  /-- The input-independent unitaries `U_0, …, U_T`. -/
  U : Fin (T + 1) → Matrix.unitaryGroup ((ι × κ) × W) ℂ

namespace QueryAlg

variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
  [DecidableEq W] {T : ℕ}

/-- de Wolf p.111 (§12.1): the state `|ψ_x^t⟩ = U_t O U_{t−1} ⋯ U_1 O U_0 |start⟩` after `U_t`
has been applied, for the oracle `O` (acting on the query register, identity on the
workspace). -/
noncomputable def stateAt (A : QueryAlg ι κ W T) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    Fin (T + 1) → EuclideanSpace ℂ ((ι × κ) × W) :=
  Fin.induction (act (A.U 0 : Matrix _ _ ℂ) A.start)
    (fun i ψ => act (A.U i.succ : Matrix _ _ ℂ)
      (act (Matrix.kronecker O (1 : Matrix W W ℂ)) ψ))

/-- The final state `U_T O ⋯ O U_0 |start⟩`. -/
noncomputable def finalState (A : QueryAlg ι κ W T) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    EuclideanSpace ℂ ((ι × κ) × W) :=
  A.stateAt O (Fin.last T)

/-- de Wolf p.111 (§12.1), Childs p.106 (§21.2), p.134 (§26.2): the probability that the
algorithm outputs `b`, when it measures its whole register in the computational basis and
outputs `out` of the outcome (a designated output qubit, membership in an accepting set, or a
list of output pairs). -/
noncomputable def outputProb {β : Type*} [DecidableEq β] (A : QueryAlg ι κ W T)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (out : (ι × κ) × W → β) (b : β) : ℝ :=
  probEvent (A.finalState O) fun z => out z = b

/-- de Wolf p.26 (§2.2), p.111 (§12.1: "computes f with error probability `≤ ε` for each
`x ∈ D`"): with standard queries to `x`, the algorithm computes the (partial) Boolean function
`f` on the domain `D` with worst-case error at most `ε`: for every `x ∈ D` (not on average,
trap Q5) it outputs `f x` with probability `≥ 1 − ε`. Values of `f` outside `D` are never read.
Bounded error is `ε = 1/3`. -/
def ComputesWithError (A : QueryAlg ι Bool W T) (out : (ι × Bool) × W → Bool)
    (D : Finset (ι → Bool)) (f : (ι → Bool) → Bool) (ε : ℝ) : Prop :=
  ∀ x ∈ D, A.outputProb (xorOracle x) out (f x) ≥ 1 - ε

end QueryAlg

/-- de Wolf p.30 (§2.4.1): the Deutsch–Jozsa "constant" case: all `x_i` have the same value. -/
def IsConstant {ι : Type*} (x : ι → Bool) : Prop :=
  ∀ i j, x i = x j

/-- de Wolf p.30 (§2.4.1): the Deutsch–Jozsa "balanced" case: `N/2` of the `x_i` are `0` and `N/2`
are `1`, written `2 |x| = N` without natural-number division (so for `N = 1` no input is
balanced). -/
def IsBalanced {ι : Type*} [Fintype ι] (x : ι → Bool) : Prop :=
  2 * hammingWeight x = Fintype.card ι

/-- de Wolf p.30 (§2.4.1), p.31 (§2.4.2): the final state `H^{⊗n} O_{x,±} H^{⊗n} |0ⁿ⟩` of the
Deutsch–Jozsa algorithm, before the measurement; the Bernstein–Vazirani algorithm "is exactly
the same". The input is indexed by `n`-bit strings (de Wolf identifies `{0, …, N−1}` with
`{0,1}ⁿ`). -/
noncomputable def deutschJozsaState {n : ℕ} (x : Qubits n → Bool) : EuclideanSpace ℂ (Qubits n) :=
  act (hadamardN n * phaseOracle x * hadamardN n) (zeroKet n)

/-- de Wolf p.31 (§2.4.2): the Bernstein–Vazirani input `x_i = (i · a) mod 2`. -/
def bvInput {n : ℕ} (a : Qubits n) : Qubits n → Bool :=
  fun i => dotBits i a

/-- de Wolf p.35 (§3.1), p.37 (§3.3.2): Simon's promise with mask `s`: `x_i = x_j` iff `i = j` or
`i = j ⊕ s` (`+` on bit strings is bitwise xor). The search version (§3.1) adds `s ≠ 0`; the
decision version (§3.3.2) allows `s = 0`. -/
def SimonPromise {n : ℕ} (x : Qubits n → Qubits n) (s : Qubits n) : Prop :=
  ∀ i j, x i = x j ↔ (i = j ∨ i = j + s)

/-- de Wolf p.35–36 (§3.2): one run of Simon's subroutine before the measurement: from
`|0ⁿ⟩|0ⁿ⟩`, apply `H^{⊗n}` to the first register, one string query `|i, y⟩ ↦ |i, y ⊕ x_i⟩`, and
`H^{⊗n}` to the first register. The law of the run's outcome `j` is `marginalFst` (the optional
measurement of the second register does not change it, p.36). -/
noncomputable def simonRunState {n : ℕ} (x : Qubits n → Qubits n) :
    EuclideanSpace ℂ (Qubits n × Qubits n) :=
  act (Matrix.kronecker (hadamardN n) (1 : Matrix (Qubits n) (Qubits n) ℂ) * xorOracle x *
    Matrix.kronecker (hadamardN n) (1 : Matrix (Qubits n) (Qubits n) ℂ)) (ket (0, 0))

/-! ### Sanity tests -/

example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup κ] :
    xorOracle (0 : ι → κ) = 1 := by
  ext p q
  simp [xorOracle, Matrix.one_apply, Prod.ext_iff]

/-- The standard query maps `|i, y⟩` to `|i, y + f(i)⟩`. -/
example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup κ] (f : ι → κ) (i : ι)
    (y : κ) : xorOracle f (i, y + f i) (i, y) = 1 := by
  simp [xorOracle]

theorem xorOracle_mul_neg {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup κ] (f : ι → κ) : xorOracle f * xorOracle (-f) = 1 := by
  ext ⟨i, y⟩ ⟨j, z⟩
  simp only [xorOracle, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Pi.neg_apply]
  rw [Finset.sum_eq_single (j, z + -f j)]
  · by_cases h : i = j
    · subst h; by_cases h' : y = z <;> simp [h']
    · simp [h, Prod.ext_iff]
  · rintro ⟨k, w⟩ _ hkw
    by_cases hk : k = j
    · subst hk
      have : w ≠ z + -f k := fun h => hkw (by rw [h])
      simp [this]
    · simp [hk]
  · simp

example {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Bool) :
    phaseOracle x * phaseOracle x = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; cases hx : x i <;> simp [phaseOracle, hx]
  · simp [phaseOracle, h]

/-- The controlled phase query never touches `|i, 0⟩`. -/
example {ι : Type*} [DecidableEq ι] (x : ι → Bool) (i : ι) :
    controlledPhaseOracle x (i, false) (i, false) = 1 := by
  simp [controlledPhaseOracle]

/-- A 0-query algorithm's output does not depend on the oracle. -/
example {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] (A : QueryAlg ι κ W 0) (O O' : Matrix (ι × κ) (ι × κ) ℂ) :
    A.finalState O = A.finalState O' := rfl

/-- One query: the final state is `U_1 (O ⊗ I) U_0 |start⟩`. -/
example {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] (A : QueryAlg ι κ W 1) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    A.finalState O = act (A.U 1 : Matrix _ _ ℂ)
      (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (act (A.U 0 : Matrix _ _ ℂ) A.start)) := rfl

example : IsBalanced (![true, false] : Fin 2 → Bool) ∧ ¬ IsBalanced (![true] : Fin 1 → Bool) := by
  unfold IsBalanced
  decide

/-- Simon's promise with `s = 0` says that `x` is injective. -/
example {n : ℕ} (x : Qubits n → Qubits n) : SimonPromise x 0 ↔ Function.Injective x := by
  simp only [SimonPromise, add_zero, or_self]
  exact ⟨fun h i j hij => (h i j).1 hij, fun h i j => ⟨fun hij => h hij, fun hij => hij ▸ rfl⟩⟩

end QAlgorithms
