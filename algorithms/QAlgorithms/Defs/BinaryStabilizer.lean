import QAlgorithms.Defs.QECC

/-!
# Binary standard form of a stabilizer and the encoding network (shared definition layer)

D. Gottesman, *Stabilizer codes and quantum error correction* (PhD thesis, 1997), cited
"Gottesman thesis p.N" (PDF pages), §§4.1–4.2, with the author's errata (Grassl's gate order;
controlled-`Y` read as controlled-`XZ` in the real form `Y = XZ`; every generator of sign `+1`).

Conventions. A code on `n = m + k` qubits encoding `k` qubits has `m = n − k` generators (no `ℕ`
subtraction); its binary generator matrix is the pair `(H_x | H_z)` of `m × n` matrices over `F₂`
(`H_x` the `σx` part, `H_z` the `σz` part, `σy ↦ (1|1)`). Wire `q : Fin (m + k)` is the source's
qubit `q + 1`; the source's 1-based generator `M_{i+1}` and logical `X̄_{i+1}` are index `i`.
-/

namespace QAlgorithms

open scoped Matrix

/-- Gottesman thesis p.39 (§4.1) and p.40 (eq. (3.23), cited): the generators with binary rows
`(a|b)` of `(H_x | H_z)` pairwise commute: `a · b′ + b · a′ = 0` over `F₂` for every pair of rows,
i.e. `H_x H_zᵀ + H_z H_xᵀ = 0`. -/
def SymplecticCommuting {m n : ℕ} (Hx Hz : Matrix (Fin m) (Fin n) (ZMod 2)) : Prop :=
  Hx * Hzᵀ + Hz * Hxᵀ = 0

/-- Gottesman thesis p.39 (§4.1, via §3.4): `(H_x | H_z)` is the binary generator matrix of a
stabilizer with `m` independent generators: the rows commute symplectically and the `m` rows
`(a|b) ∈ F₂^{2n}` are linearly independent. -/
def IsBinaryStabilizerMatrix {m n : ℕ} (Hx Hz : Matrix (Fin m) (Fin n) (ZMod 2)) : Prop :=
  SymplecticCommuting Hx Hz ∧ LinearIndependent (ZMod 2) (Matrix.fromCols Hx Hz)

/-- Gottesman thesis p.39 (§4.1, eq. (4.3)): the standard form
```
     r      m−r     k        r     m−r    k
r  [ I      A1      A2   |   B     C1     C2 ]
m−r[ 0      0       0    |   D     I      E  ]
```
with `r ≤ m`: the `σx` half has the identity `I_r` in rows and columns `< r` and zero rows `≥ r`;
the `σz` half has the identity `I_{m−r}` in rows `≥ r` and columns `[r, m)`; the blocks
`A1, A2, B, C1, C2, D, E` are arbitrary. -/
def IsStandardForm {m k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) : Prop :=
  r ≤ m ∧
    (∀ (i : Fin m) (j : Fin (m + k)), (i : ℕ) < r → (j : ℕ) < r →
      Hx i j = if (i : ℕ) = (j : ℕ) then 1 else 0) ∧
    (∀ (i : Fin m) (j : Fin (m + k)), r ≤ (i : ℕ) → Hx i j = 0) ∧
    (∀ (i : Fin m) (j : Fin (m + k)), r ≤ (i : ℕ) → r ≤ (j : ℕ) → (j : ℕ) < m →
      Hz i j = if (i : ℕ) = (j : ℕ) then 1 else 0)

/-- Gottesman thesis p.41 (§4.2): the tensor product `M_0 ⊗ ⋯ ⊗ M_{n−1}` of one single-qubit
operator per qubit (factor `q` on wire `q`). -/
def kronAll {n : ℕ} (M : Fin n → Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ q, M q (y q) (z q)

/-- Gottesman thesis p.41 (§4.2) with the author's errata: the sign-`+1` Pauli operator of the
binary row `(a|b)` in the real form, `⊗_q σz^{b_q} σx^{a_q}` (`σx` applied first; a `σy` factor is
`σzσx`, the errata's "controlled-XZ"). This is the only convention under which the page's
"performing `σz` after the Hadamard transform" is correct. -/
def rowPauli {n : ℕ} (a b : Fin n → ZMod 2) : Matrix (Qubits n) (Qubits n) ℂ :=
  kronAll fun q => (if b q = 1 then pauliZ else 1) * (if a q = 1 then pauliX else 1)

/-- Gottesman thesis p.40 (§4.1, "Suppose we pick `U3 = I`. Then we can take `V3 = 0`, and by
equation (4.5), `U2 = Eᵀ` and `V1 = EᵀC1ᵀ + C2ᵀ`"): the binary row (`σx` part, `σz` part) of the
standard-form logical `X̄_i`, `i : Fin k`. With the blocks of `H_z` (`C1`: rows `< r`, columns
`[r, m)`; `C2`: rows `< r`, columns `≥ m`; `E`: rows `[r, m)`, columns `≥ m`), the `σx` part is
`0` on columns `< r`, `E_{j−r, i}` on columns `j ∈ [r, m)` and `δ_{ij}` on column `m + j`; the
`σz` part is `(EᵀC1ᵀ + C2ᵀ)_{ij} = Σ_{l ∈ [r, m)} E_{l−r, i} (C1)_{j, l−r} + (C2)_{j i}` on
columns `j < r` and `0` elsewhere. (`H_x` does not enter.) -/
def logicalXRow {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (i : Fin k) :
    (Fin (m + k) → ZMod 2) × (Fin (m + k) → ZMod 2) :=
  (fun j => if h : (j : ℕ) < m then
      (if r ≤ (j : ℕ) then Hz ⟨j, h⟩ (Fin.natAdd m i) else 0)
    else if (j : ℕ) = m + (i : ℕ) then 1 else 0,
   fun j => if h : (j : ℕ) < r ∧ (j : ℕ) < m then
      (∑ l : Fin m, if r ≤ (l : ℕ) then Hz l (Fin.natAdd m i) * Hz ⟨j, h.2⟩ (Fin.castAdd k l) else 0) +
        Hz ⟨j, h.2⟩ (Fin.natAdd m i)
    else 0)

/-- Gottesman thesis p.40 (§4.1): the standard-form logical operator `X̄_i` (sign `+1`, real
form). -/
def logicalX {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (i : Fin k) :
    Matrix (Qubits (m + k)) (Qubits (m + k)) ℂ :=
  rowPauli (logicalXRow r Hz i).1 (logicalXRow r Hz i).2

/-- Gottesman thesis p.41 (§4.2, eqs. (4.7)–(4.8)): the encoded basis state
`(I + M_1) ⋯ (I + M_{n−k}) X̄_1^{c_1} ⋯ X̄_k^{c_k} |0 … 0⟩`, unnormalized, with `M_i` the sign-`+1`
operators of the rows of `(H_x | H_z)`. Products are frozen `orderedProd`s; their factors commute,
so the order is immaterial. -/
noncomputable def stabEncodedState {m k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (c : Qubits k) : EuclideanSpace ℂ (Qubits (m + k)) :=
  act (orderedProd fun i : Fin m => 1 + rowPauli (Hx i) (Hz i))
    (act (orderedProd fun i : Fin k => if c i then logicalX r Hz i else 1) (zeroKet (m + k)))

/-- Gottesman thesis pp.41–42 (§4.2): the gates of the encoding network: the Hadamard transform
`R` (4.12), `σz`, and the controlled gates `σz^b σx^a` for `(a, b) ≠ (0, 0)` (controlled-`σx` =
CNOT, controlled-`σz`, controlled-`σzσx`), the control on the first qubit (frozen
`controlled`). -/
def stabEncoderGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 pauliZ} ∪
    {g | ∃ a b : Bool, (a, b) ≠ (false, false) ∧
      g = Gate.ofMatrix2 (controlled ((if b then pauliZ else 1) * (if a then pauliX else 1)))}

/-- Gottesman thesis p.42 (§4.2): the controlled gate `σz^b σx^a` with control wire `c` and target
wire `t` (helper for `stabEncoder`). -/
def stabCtrlApp {N : ℕ} (a b : Bool) (hab : (a, b) ≠ (false, false)) (c t : Fin N) (h : c ≠ t) :
    GateApp stabEncoderGateSet N :=
  ⟨Gate.ofMatrix2 (controlled ((if b then pauliZ else 1) * (if a then pauliX else 1))),
    Set.mem_union_right _ ⟨a, b, hab, rfl⟩, Stabilizer.wire2 c t h⟩

theorem castAdd_ne_natAdd {m k : ℕ} (j : Fin m) (i : Fin k) : Fin.natAdd m i ≠ Fin.castAdd k j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
  omega

/-- Gottesman thesis pp.41–43 (§4.2) with the author's errata: the encoding network as a frozen
`Circuit` (head of the list applied first) on `m + k` wires, input `|0 … 0⟩|c⟩` (`c` on wires
`m, …, m + k − 1`).
1. For each `i < k` and each `j ∈ [r, m)` with `E_{j−r, i} = (H_z)_{j, m+i} = 1`, a CNOT from wire
   `m + i` to wire `j` (the `σx` part of `X̄_i` conditioned on `c_i`; its `σz` part acts trivially
   on `|0⟩`).
2. Then, for `i = 0, …, r − 1` in turn: `R` on wire `i`, `σz` on wire `i` if `B_ii = (H_z)_{ii} = 1`,
   and for every wire `q ≠ i` on which `M_i` acts, the gate `σz^{(H_z)_{iq}} σx^{(H_x)_{iq}}`
   controlled on wire `i` (errata: the Hadamard on qubit `i` immediately precedes its control dots).
No gates for the generators `i ≥ r` (products of `σz`, p.42). -/
noncomputable def stabEncoder {m k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) :
    Circuit stabEncoderGateSet (m + k) :=
  ((List.finRange k).flatMap fun (i : Fin k) => (List.finRange m).filterMap fun (j : Fin m) =>
      if r ≤ (j : ℕ) ∧ Hz j (Fin.natAdd m i) = 1 then
        some (stabCtrlApp true false (by simp) (Fin.natAdd m i) (Fin.castAdd k j)
          (castAdd_ne_natAdd j i))
      else none) ++
  ((List.finRange m).flatMap fun (i : Fin m) =>
    if (i : ℕ) < r then
      [⟨Gate.ofMatrix1 hadamard, Set.mem_union_left _ (Set.mem_insert _ _),
          Stabilizer.wire1 (Fin.castAdd k i)⟩] ++
      (if Hz i (Fin.castAdd k i) = 1 then
        [⟨Gate.ofMatrix1 pauliZ, Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl),
          Stabilizer.wire1 (Fin.castAdd k i)⟩] else []) ++
      (List.finRange (m + k)).filterMap fun (q : Fin (m + k)) =>
        if h : q ≠ Fin.castAdd k i ∧
            (decide (Hx i q = 1), decide (Hz i q = 1)) ≠ (false, false) then
          some (stabCtrlApp (decide (Hx i q = 1)) (decide (Hz i q = 1)) h.2
            (Fin.castAdd k i) q (Ne.symm h.1))
        else none
    else [])

/-! ### Sanity tests -/

example {n : ℕ} : rowPauli (0 : Fin n → ZMod 2) 0 = 1 := by
  ext y z
  simp [rowPauli, kronAll, Matrix.one_apply, Finset.prod_boole, funext_iff]

example : rowPauli (![1] : Fin 1 → ZMod 2) ![0] = (Gate.ofMatrix1 pauliX).mat := by
  ext y z
  simp [rowPauli, kronAll, Gate.ofMatrix1]

example {k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin 0) (Fin (0 + k)) (ZMod 2)) :
    stabEncoder r Hx Hz = [] := by
  simp [stabEncoder]

example {k : ℕ} (Hz : Matrix (Fin 0) (Fin (0 + k)) (ZMod 2)) (i : Fin k) (j : Fin (0 + k)) :
    (logicalXRow 0 Hz i).1 j = (if (j : ℕ) = (i : ℕ) then 1 else 0) ∧
      (logicalXRow 0 Hz i).2 j = 0 := by
  simp [logicalXRow]

example {k : ℕ} (Hx Hz : Matrix (Fin 0) (Fin (0 + k)) (ZMod 2)) : IsStandardForm 0 Hx Hz := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

example : SymplecticCommuting (!![1, 0] : Matrix (Fin 1) (Fin 2) (ZMod 2)) !![0, 1] := by
  unfold SymplecticCommuting
  decide

end QAlgorithms
