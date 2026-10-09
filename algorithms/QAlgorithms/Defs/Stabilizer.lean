import QAlgorithms.Defs.LocalHamiltonian

/-!
# Stabilizer states, measurement-controlled Clifford circuits, classical samplers
(shared definition layer)

de Wolf §20.1–20.3 (pp.185–188), for the Gottesman–Knill theorem (Theorem 6).
-/

namespace QAlgorithms.Stabilizer

open scoped NNReal

open QAlgorithms.Complexity

/-- de Wolf p.185 (§20.1): the one-qubit Paulis `I, X, Y, Z`. -/
inductive Pauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq

/-- The matrix of a one-qubit Pauli (`pauliX`, `pauliY`, `pauliZ` of the Gates module). -/
def Pauli.mat : Pauli → Matrix Bool Bool ℂ
  | .I => 1
  | .X => pauliX
  | .Y => pauliY
  | .Z => pauliZ

/-- The product of two one-qubit Paulis, as `i^c · R` (`XY = iZ`, `YX = −iZ`, `YZ = iX`, `ZY = −iX`,
`ZX = iY`, `XZ = −iY`; `P P = I`). -/
def Pauli.mul : Pauli → Pauli → ZMod 4 × Pauli
  | .I, q => (0, q)
  | p, .I => (0, p)
  | .X, .X => (0, .I)
  | .Y, .Y => (0, .I)
  | .Z, .Z => (0, .I)
  | .X, .Y => (1, .Z)
  | .Y, .X => (3, .Z)
  | .Y, .Z => (1, .X)
  | .Z, .Y => (3, .X)
  | .Z, .X => (1, .Y)
  | .X, .Z => (3, .Y)

/-- de Wolf p.185 (§20.1: "`P_n = {+1, −1, +i, −i} · {I, X, Y, Z}^{⊗n}`"): an `n`-qubit Pauli with
phase `i^phase`. -/
structure PauliString (n : ℕ) where
  /-- The phase exponent: the factor is `i^phase ∈ {1, i, −1, −i}`. -/
  phase : ZMod 4
  /-- The one-qubit Pauli on each wire. -/
  ops : Fin n → Pauli

/-- The `2ⁿ × 2ⁿ` matrix `i^phase · P_1 ⊗ ⋯ ⊗ P_n` (wire `0` is the first factor). -/
noncomputable def PauliString.toMatrix {n : ℕ} (P : PauliString n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => Complex.I ^ P.phase.val * ∏ q : Fin n, (P.ops q).mat (y q) (z q)

/-- The (symbolic) product of two Pauli strings, wire by wire, with the phases collected. -/
def PauliString.mul {n : ℕ} (P Q : PauliString n) : PauliString n :=
  ⟨P.phase + Q.phase + ∑ q : Fin n, (Pauli.mul (P.ops q) (Q.ops q)).1,
    fun q => (Pauli.mul (P.ops q) (Q.ops q)).2⟩

/-- de Wolf p.185: two Pauli strings commute (as matrices). -/
def PauliString.Commute {n : ℕ} (P Q : PauliString n) : Prop :=
  P.toMatrix * Q.toMatrix = Q.toMatrix * P.toMatrix

/-- de Wolf p.185, p.187: a stabilizer description of an `n`-qubit state: `n` Pauli strings. -/
abbrev Tableau (n : ℕ) := Fin n → PauliString n

/-- The ordered product `Π_{i ∈ s} T_i` (increasing `i`) of the matrices of a subfamily. -/
noncomputable def subProd {n : ℕ} (T : Tableau n) (s : Finset (Fin n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun i : Fin n => if i ∈ s then (T i).toMatrix else 1).prod

/-- de Wolf p.185 (§20.1 and footnote 2): `T` describes a stabilizer state: its `n` elements have
phases `±1`, pairwise commute, are independent (no element is `±1, ±i` times a product of some
other elements), and `−I` is not a product of some of them. -/
def IsValidTableau {n : ℕ} (T : Tableau n) : Prop :=
  (∀ j, (T j).phase = 0 ∨ (T j).phase = 2) ∧
  (∀ i j, (T i).Commute (T j)) ∧
  (∀ (j : Fin n) (s : Finset (Fin n)), j ∉ s → ∀ c : ZMod 4,
    (T j).toMatrix ≠ Complex.I ^ c.val • subProd T s) ∧
  ∀ s : Finset (Fin n), subProd T s ≠ -1

/-- de Wolf p.185 (footnote 3: "this global phase wouldn't even be there if we took the density
matrix view"): `Π_j (I + T_j)/2`, which for a valid tableau is the projector `|ψ⟩⟨ψ|` onto the
unique stabilized state. -/
noncomputable def tableauProjector {n : ℕ} (T : Tableau n) : Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun j : Fin n => (2⁻¹ : ℂ) • (1 + (T j).toMatrix)).prod

/-- Two bits for a one-qubit Pauli: `I = 00`, `X = 10`, `Y = 11`, `Z = 01`. -/
def encPauli : Pauli → Str
  | .I => [false, false]
  | .X => [true, false]
  | .Y => [true, true]
  | .Z => [false, true]

/-- The Pauli encoded by two bits (inverse of `encPauli`). -/
def pauliOfBits : Bool → Bool → Pauli
  | false, false => .I
  | true, false => .X
  | true, true => .Y
  | false, true => .Z

/-- Two bits for a phase exponent `c ∈ ZMod 4` (its value in binary, high bit first). -/
def encPhase (c : ZMod 4) : Str :=
  [decide (2 ≤ c.val), decide (c.val % 2 = 1)]

/-- de Wolf p.187 ("`n` stabilizers, which can be written down with `n × (2n + 2)` bits"): the
encoding of a tableau: for each stabilizer, two phase bits and two bits per qubit. -/
def encodeTableau {n : ℕ} (T : Tableau n) : Str :=
  (List.ofFn fun j : Fin n => encPhase (T j).phase ++ (List.ofFn fun q => encPauli ((T j).ops q)).flatten).flatten

/-- Reads a tableau from the first `n(2n + 2)` bits of a string (missing bits read as `0`);
the inverse of `encodeTableau`. -/
def decodeTableau (n : ℕ) (s : Str) : Tableau n :=
  fun j => ⟨(if s.getD (j * (2 * n + 2)) false then 2 else 0) +
      (if s.getD (j * (2 * n + 2) + 1) false then 1 else 0),
    fun q => pauliOfBits (s.getD (j * (2 * n + 2) + 2 + 2 * q) false)
      (s.getD (j * (2 * n + 2) + 3 + 2 * q) false)⟩

/-- de Wolf p.186 (§20.2): the operations of a measurement-controlled Clifford circuit on `n`
qubits: a Pauli gate, `H`, `S`, `CNOT` (control `c`, target `t`), or the measurement of a Pauli
`M ∈ {I, X, Y, Z}^{⊗n}` (projectors `(I ± M)/2`). -/
inductive CliffordOp (n : ℕ) where
  | pauli (q : Fin n) (P : Pauli)
  | h (q : Fin n)
  | s (q : Fin n)
  | cnot (c t : Fin n) (hct : c ≠ t)
  | measure (M : Fin n → Pauli)

/-- The single wire `q` as an embedding `Fin 1 ↪ Fin n`. -/
def wire1 {n : ℕ} (q : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => q, fun a b _ => Subsingleton.elim a b⟩

/-- The wires `(c, t)`, `c ≠ t`, as an embedding `Fin 2 ↪ Fin n`. -/
def wire2 {n : ℕ} (c t : Fin n) (hct : c ≠ t) : Fin 2 ↪ Fin n :=
  ⟨Fin.cons c fun _ : Fin 1 => t,
    Fin.cons_injective_iff.2 ⟨by rintro ⟨_, h⟩; exact hct h.symm, fun a b _ => Subsingleton.elim a b⟩⟩

/-- The unitary of a gate operation (the identity for a measurement, which is handled separately). -/
noncomputable def CliffordOp.mat {n : ℕ} : CliffordOp n → Matrix (Qubits n) (Qubits n) ℂ
  | .pauli q P => embedOp (Gate.ofMatrix1 P.mat).mat (wire1 q)
  | .h q => embedOp (Gate.ofMatrix1 hadamard).mat (wire1 q)
  | .s q => embedOp (Gate.ofMatrix1 phaseS).mat (wire1 q)
  | .cnot c t hct => embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct)
  | .measure _ => 1

/-- Self-delimiting code of a bit list: each bit `β` as `1β`, then `00`. -/
def encBits (l : List Bool) : Str :=
  l.flatMap (fun β => [true, β]) ++ [false, false]

/-- Code of a transcript: `100` for a gate step, `11β` for a measurement with outcome `β`, then `0`. -/
def encHist (hist : List (Option Bool)) : Str :=
  hist.flatMap (fun o => match o with
    | none => [true, false, false]
    | some β => [true, true, β]) ++ [false]

/-- Code of the controller's input `(n, r, transcript)`, with `n` in unary. -/
def encCtrlInput (n : ℕ) (r : List Bool) (hist : List (Option Bool)) : Str :=
  encNat n ++ encBits r ++ encHist hist

/-- Code of the controller's answer: `0` for "halt", otherwise `1`, a tag, and the arguments. -/
def encOp {n : ℕ} : Option (CliffordOp n) → Str
  | none => [false]
  | some (.pauli q P) => [true] ++ encNat 0 ++ encNat q ++ encPauli P
  | some (.h q) => [true] ++ encNat 1 ++ encNat q
  | some (.s q) => [true] ++ encNat 2 ++ encNat q
  | some (.cnot c t _) => [true] ++ encNat 3 ++ encNat c ++ encNat t
  | some (.measure M) => [true] ++ encNat 4 ++ (List.ofFn fun q => encPauli (M q)).flatten

/-- de Wolf p.186–187 (§20.2: "we can then let the next gate depend on the earlier measurement
outcomes, using some polynomial-time classical (possibly randomized) algorithm to compute what the
next gate or measurement would be"; "strictly speaking we'd have to talk about families of
circuits `{C_n}`"): a family of measurement-controlled Clifford circuits. On `n` qubits, with random
bits `r` (`rbits(n)` of them) and the transcript of the steps so far (`none` for a gate, `some β`
for a measurement with outcome `β`, `false` meaning `+1`), the controller names the next operation
or halts (`none`); it halts after at most `steps(n)` operations, and it is computable in
polynomial time from `(n, r, transcript)` (`n` in unary). -/
structure MCCFamily where
  /-- The number of random bits, a polynomial in `n`. -/
  rbits : Polynomial ℕ
  /-- The bound on the number of operations, a polynomial in `n`. -/
  steps : Polynomial ℕ
  /-- The classical controller. -/
  ctrl : (n : ℕ) → List Bool → List (Option Bool) → Option (CliffordOp n)
  /-- It halts within `steps(n)` operations. -/
  halts : ∀ n r hist, steps.eval n ≤ hist.length → ctrl n r hist = none
  /-- It is polynomial-time computable. -/
  polytime : ∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ n r hist, g (encCtrlInput n r hist) = encOp (ctrl n r hist)

/-- One step of the run with random bits `r`: query the controller on the transcript; apply a gate,
or measure the Pauli `M` (outcome `β` with Born probability `‖(I + (−1)^β M)/2 ψ‖²`, followed by
renormalization), or halt. The `min 1` only matters for non-unit `ψ`, which a run never reaches. -/
noncomputable def MCCFamily.step (F : MCCFamily) (n : ℕ) (r : List Bool)
    (st : EuclideanSpace ℂ (Qubits n) × List (Option Bool)) :
    PMF (EuclideanSpace ℂ (Qubits n) × List (Option Bool)) :=
  match F.ctrl n r st.2 with
  | none => PMF.pure st
  | some (.measure M) =>
      let proj : Bool → Matrix (Qubits n) (Qubits n) ℂ := fun β =>
        (2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))
      (PMF.bernoulli (min 1 (Real.toNNReal (‖act (proj true) st.1‖ ^ 2))) (min_le_left _ _)).map
        fun β => (((‖act (proj β) st.1‖)⁻¹ : ℝ) • act (proj β) st.1, st.2 ++ [some β])
  | some op => PMF.pure (act op.mat st.1, st.2 ++ [none])

/-- The law of the state after `k` steps, from `|x⟩` with random bits `r`. -/
noncomputable def MCCFamily.run (F : MCCFamily) (n : ℕ) (r : List Bool) (x : Qubits n) :
    ℕ → PMF (EuclideanSpace ℂ (Qubits n) × List (Option Bool))
  | 0 => PMF.pure (ket x, [])
  | k + 1 => (F.run n r x k).bind (F.step n r)

/-- de Wolf p.187 (§20.2–20.3: the circuit "samples from a probability distribution over
stabilizer states"): the law of the final state `|ψ_final⟩⟨ψ_final|` (a density matrix, so the
global phase is discarded) when the circuit runs on `|x⟩` with uniformly random bits `r` and Born
measurement outcomes. -/
noncomputable def MCCFamily.finalDist (F : MCCFamily) (n : ℕ) (x : Qubits n) :
    PMF (Matrix (Qubits n) (Qubits n) ℂ) :=
  (PMF.uniformOfFintype (Fin (F.rbits.eval n) → Bool)).bind fun r =>
    (F.run n (List.ofFn r) x (F.steps.eval n)).map fun st => pureDensity st.1

/-- de Wolf p.26 (§2.2: randomized algorithms receive random bits as an extra input), p.187
(Theorem 6: "a classical polynomial-time algorithm that … samples"): a classical randomized
polynomial-time algorithm: a polynomial-time computable `f` run on the input followed by
`rbits(|w|)` uniformly random bits. -/
structure RandPolyTimeSampler where
  /-- The number of random bits, a polynomial in the input length. -/
  rbits : Polynomial ℕ
  /-- The deterministic polynomial-time part. -/
  f : Str → Str
  /-- `f` is polynomial-time computable. -/
  polytime : PolyTimeComputable f

/-- The output distribution of the sampler on input `w`. -/
noncomputable def RandPolyTimeSampler.outDist (A : RandPolyTimeSampler) (w : Str) : PMF Str :=
  (PMF.uniformOfFintype (Fin (A.rbits.eval w.length) → Bool)).map fun r => A.f (w ++ encBits (List.ofFn r))

/-- The input `(n, x)` of the simulator: `n` in unary, then the bits of `x`. -/
def encInput (n : ℕ) (x : Qubits n) : Str :=
  encNat n ++ List.ofFn x

/-! ### Sanity tests -/

example : Pauli.mul .X .Y = (1, .Z) := rfl

/-- `XY = iZ` as matrices, matching `Pauli.mul .X .Y = (1, .Z)`. -/
example : pauliX * pauliY = Complex.I • pauliZ := by
  ext a b
  cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool]

/-- The one-qubit `Z` stabilizer `+Z` projects onto `|0⟩`: `(I + Z)/2 = |0⟩⟨0|`. -/
example : tableauProjector (fun _ : Fin 1 => (⟨0, fun _ => .Z⟩ : PauliString 1))
    (fun _ => false) (fun _ => false) = 1 := by
  simp [tableauProjector, PauliString.toMatrix, Pauli.mat, pauliZ]
  norm_num

/-- Encoding then decoding a tableau gives it back (here `n = 1`, the stabilizer `−Y`). -/
example : (decodeTableau 1 (encodeTableau fun _ : Fin 1 => (⟨2, fun _ => .Y⟩ : PauliString 1)) 0).phase
    = 2 ∧ (decodeTableau 1 (encodeTableau fun _ : Fin 1 => (⟨2, fun _ => .Y⟩ : PauliString 1)) 0).ops 0
    = .Y := by
  decide

/-- With zero steps, a circuit outputs its initial basis state. -/
example (F : MCCFamily) (n : ℕ) (r : List Bool) (x : Qubits n) : F.run n r x 0 = PMF.pure (ket x, []) :=
  rfl

end QAlgorithms.Stabilizer
