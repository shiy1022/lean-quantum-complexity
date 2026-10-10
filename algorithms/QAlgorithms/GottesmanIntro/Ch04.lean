import QAlgorithms.Defs.BinaryStabilizer

/-!
# Gottesman, *An introduction to quantum error correction*, §4.4: Steane error correction

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages): Claim 1 (p.28), inside
the proof that Steane error correction satisfies property EC A.

The Steane EC circuit (p.27, Figure 3) is needed only here, so it is a chunk-local definition.
The joint register is indexed by `(Qubits n × R) × (Qubits n × Qubits n)`: the data block with a
reference system `R` (the data may be entangled with it), then the phase ancilla block and the
bit-flip ancilla block. Qubit `i` of every block is wire `i`.
-/

namespace QAlgorithms.GottesmanIntro

/-- Transversal CNOT between two `n`-qubit blocks (Gottesman intro p.27, Figure 3): the frozen
two-qubit `cnot` applied to qubit `i` of both blocks for every `i`; the first block is the
control, the second the target, i.e. `|c, t⟩ ↦ |c, t ⊕ c⟩`. -/
def transCnot (n : ℕ) : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  Matrix.of fun p q => ∏ i : Fin n, cnot (p.1 i, p.2 i) (q.1 i, q.2 i)

/-- An operator on two `n`-qubit blocks acts only on qubit `i` of both blocks for `i ∈ g`
(Gottesman intro p.28: "each such faulty gate location can affect both the corresponding data
qubit and ancilla qubit"): read as an operator on `n + n` qubits (first block = first `n`
wires), it acts within the wires `{i, n + i : i ∈ g}`. -/
def ActsWithinPair {n : ℕ} (g : Finset (Fin n))
    (G : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) : Prop :=
  ∃ G' : Matrix (Qubits (n + n)) (Qubits (n + n)) ℂ,
    ActsWithin (g.image (Fin.castAdd n) ∪ g.image (Fin.natAdd n)) G' ∧
      G = G'.submatrix (qubitsAppendEquiv n n).symm (qubitsAppendEquiv n n).symm

/-- An operator on (data block, phase ancilla block), lifted to the joint register (identity on
the reference and on the bit-flip ancilla). -/
def liftDataPhase {n : ℕ} {R : Type*} [DecidableEq R]
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    Matrix ((Qubits n × R) × (Qubits n × Qubits n)) ((Qubits n × R) × (Qubits n × Qubits n)) ℂ :=
  Matrix.of fun p q =>
    if p.1.2 = q.1.2 ∧ p.2.2 = q.2.2 then M (p.1.1, p.2.1) (q.1.1, q.2.1) else 0

/-- An operator on (data block, bit-flip ancilla block), lifted to the joint register (identity
on the reference and on the phase ancilla). -/
def liftDataBit {n : ℕ} {R : Type*} [DecidableEq R]
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    Matrix ((Qubits n × R) × (Qubits n × Qubits n)) ((Qubits n × R) × (Qubits n × Qubits n)) ℂ :=
  Matrix.of fun p q =>
    if p.1.2 = q.1.2 ∧ p.2.1 = q.2.1 then M (p.1.1, p.2.2) (q.1.1, q.2.2) else 0

/-- The (unnormalized) data ⊗ reference state after faulty Steane error correction on the CSS
code of `C1, C2` (Gottesman intro p.27–28), in the branch where the phase ancilla gives outcome
`wP` and the bit-flip ancilla outcome `wB`:

1. the phase ancilla is the encoded `|0⟩ = Σ_{w ∈ C2⊥} |w⟩` with the preparation errors `FP`,
   the bit-flip ancilla the encoded `|0⟩ + |1⟩ = Σ_{u ∈ C1} |u⟩` with the preparation errors
   `FB`; the incoming data ⊗ reference vector is `ψ`;
2. transversal CNOT with the phase ancilla as control and the data as target, followed by the
   CNOT faults `GP` on (data, phase ancilla);
3. transversal CNOT with the data as control and the bit-flip ancilla as target, followed by the
   CNOT faults `GB` on (data, bit-flip ancilla);
4. transversal Hadamard on the phase ancilla, then the faults `HP` (Hadamard and measurement of
   the phase ancilla) and `HB` (measurement of the bit-flip ancilla);
5. both ancillas measured in the standard basis, projected on outcomes `wP`, `wB`;
6. the classical decoders give `d = decP wP` (as a `C2` word with errors) and `decB wB` (as a
   `C1` word with errors), and the correction `Z` on the qubits of `decP wP` and `X` on the
   qubits of `decB wB` is applied to the data (fault-free, p.28). -/
noncomputable def steaneECOutput {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2))
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (FP FB HP HB : Matrix (Qubits n) (Qubits n) ℂ)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (ψ : EuclideanSpace ℂ (Qubits n × R)) (wP wB : Fin n → ZMod 2) :
    EuclideanSpace ℂ (Qubits n × R) :=
  let s0 := tensorVec ψ (tensorVec (act FP (cssZeroState C2)) (act FB (cssPlusState C1)))
  let s1 := act (liftDataPhase (R := R) (GP * (transCnot n).submatrix Prod.swap Prod.swap)) s0
  let s2 := act (liftDataBit (R := R) (GB * transCnot n)) s1
  let s3 := act (Matrix.kronecker (1 : Matrix (Qubits n × R) (Qubits n × R) ℂ)
    (Matrix.kronecker (HP * hadamardN n) HB)) s2
  let v : EuclideanSpace ℂ (Qubits n × R) :=
    WithLp.toLp 2 fun p => s3 (p, (bitsOfZMod wP, bitsOfZMod wB))
  act (Matrix.kronecker (rowPauli (decB wB) (decP wP)) (1 : Matrix R R ℂ)) v

/-- Gottesman intro p.28, Claim 1 (Steane error correction, proof of EC A): let `C1, C2 ⊆ F_2^n`
be binary linear codes with `C2⊥ ⊆ C1` and let `C` be their CSS code (p.11). Run Steane error
correction (p.27, Figure 3) on an arbitrary incoming data vector `ψ`, possibly entangled with a
reference system `R`, with classical decoders returning an error with the same syndrome as the
measured word (`decP` for `C2`, `decB` for `C1`, p.28). Let the faults be arbitrary operators:
`FP`, `FB` on the prepared phase and bit-flip ancillas, acting within the qubit sets `fP`, `fB`;
`GP`, `GB` at the transversal CNOTs, acting within qubit `i` of the data block and of the
ancilla for `i ∈ gP`, resp. `gB`; `HP`, `HB` during the Hadamard and measurement of the phase
ancilla and the measurement of the bit-flip ancilla, within `hP`, `hB`. Then for every pair of
measurement outcomes the corrected data ⊗ reference state lies in `V_F ⊗ R`, where
`F = fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB` and `V_F` is the span of the vectors `E|c⟩` with `c ∈ C` and
`E` acting within `F`: the final state has errors only on the qubits of `F`; and `|F| ≤ s`,
`s = |fP| + |fB| + |gP| + |gB| + |hP| + |hB|`. -/
theorem steaneEC_claim1 {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2)) (hC : binDual C2 ≤ C1)
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hdecP : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C2, h ⬝ᵥ decP w = h ⬝ᵥ w)
    (hdecB : ∀ w : Fin n → ZMod 2, ∀ h ∈ binDual C1, h ⬝ᵥ decB w = h ⬝ᵥ w)
    (fP fB gP gB hP hB : Finset (Fin n))
    (FP FB HP HB : Matrix (Qubits n) (Qubits n) ℂ)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (hFP : ActsWithin fP FP) (hFB : ActsWithin fB FB)
    (hGP : ActsWithinPair gP GP) (hGB : ActsWithinPair gB GB)
    (hHP : ActsWithin hP HP) (hHB : ActsWithin hB HB)
    (ψ : EuclideanSpace ℂ (Qubits n × R)) (wP wB : Fin n → ZMod 2) :
    steaneECOutput C1 C2 decP decB FP FB HP HB GP GB ψ wP wB ∈
        errorSpaceWithRef R (cssCode C1 C2) (fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB) ∧
      (fP ∪ fB ∪ gP ∪ gB ∪ hP ∪ hB).card ≤
        fP.card + fB.card + gP.card + gB.card + hP.card + hB.card := by
  sorry

end QAlgorithms.GottesmanIntro
