import QAlgorithms.Defs.Information

/-!
# The quantum linear systems problem (shared definition layer)

Childs, Kothari, Somma, *Quantum linear systems algorithm with exponentially improved dependence
on precision*, SIAM J. Comput. 2017 (arXiv:1511.02306v2), cited "CKS p.N" (PDF pages).

Indexing: the source's `[N] = {1, …, N}` is `Fin N` (0-based); index `j` is held in
`n = ⌈log₂ N⌉ = Nat.clog 2 N` qubits as the `n`-bit most-significant-first expansion
`natToBits n j`.
-/

namespace QAlgorithms

/-- CKS p.3 (§1.1): `A` is `d`-sparse: at most `d` nonzero entries in any row or column. -/
def IsSparse {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) : Prop :=
  (∀ j, (Finset.univ.filter fun k => A j k ≠ 0).card ≤ d) ∧
    ∀ k, (Finset.univ.filter fun j => A j k ≠ 0).card ≤ d

/-- CKS p.3 (§1.1): the condition number `σ_max(A)/σ_min(A)`, the ratio of the largest to the
smallest singular value (singular values = square roots of the eigenvalues of `A†A`, which are
nonnegative). The source leaves it undefined for non-invertible `A`; there the formula divides by
`0` and returns `0`, so statements assume `A` invertible (and a nonempty index type). For
Hermitian `A` it is `max |λ| / min |λ|`. -/
noncomputable def conditionNumber {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  if h : 0 < Fintype.card ι then
    Real.sqrt (ascEigenvalues (A.conjTranspose * A) ⟨Fintype.card ι - 1, by omega⟩) /
      Real.sqrt (ascEigenvalues (A.conjTranspose * A) ⟨0, h⟩)
  else 0

/-- CKS p.2–3 ((3)): the normalized state `|b⟩ = Σ_i b_i |i⟩ / ‖Σ_i b_i |i⟩‖` (statements require
`b ≠ 0`; at `b = 0` the value is `0`). -/
noncomputable def normalizedVec {ι : Type*} [Fintype ι] (b : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  ((‖b‖⁻¹ : ℝ) : ℂ) • b

/-- CKS p.2 (§1.1): a vector indexed by `[N]` placed on an `n`-qubit register: amplitude `v_i` at
the `n`-bit string of `i` and `0` at the strings encoding numbers `≥ N` (meaningful for
`N ≤ 2ⁿ`). -/
noncomputable def padState {N : ℕ} (n : ℕ) (v : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun z => if h : bitsToNat z < N then v ⟨bitsToNat z, h⟩ else 0

/-- The basis state `|j, l⟩` of two `n`-qubit registers (`j`, `l` written in `n` bits each). -/
noncomputable def ket2 (n j l : ℕ) : EuclideanSpace ℂ (Qubits (n + n)) :=
  ket (Fin.append (natToBits n j) (natToBits n l))

/-- CKS p.2 ((1)): `O` is a column oracle for the `d`-sparse `A`: a unitary on two `n`-qubit
registers (`n = ⌈log₂ N⌉`) performing `|j, ℓ⟩ ↦ |j, ν(j, ℓ)⟩` for `j ∈ [N]`, `ℓ ∈ [d]`, where
`ν(j, ·)` enumerates, without repetition, positions of column `j` that include all of its nonzero
entries (the "row index of the `ℓ`-th nonzero entry"; when the column has fewer than `d` nonzero
entries the remaining `ν(j, ℓ)` are other positions, as in [BCK15]). Computed in place; basis
states outside `[N] × [d]` are unconstrained. -/
def IsColumnOracle {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (d : ℕ)
    (O : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N)) (Qubits (Nat.clog 2 N + Nat.clog 2 N)) ℂ) :
    Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧
    ∃ ν : Fin N → Fin d → Fin N, (∀ j, Function.Injective (ν j)) ∧
      (∀ j k, A k j ≠ 0 → ∃ l, ν j l = k) ∧
      ∀ (j : Fin N) (l : Fin d), act O (ket2 (Nat.clog 2 N) j l) = ket2 (Nat.clog 2 N) j (ν j l)

/-- CKS p.3 ((2)): `O` is an entry oracle for `A`: a unitary performing
`|j, k, z⟩ ↦ |j, k, z ⊕ A_{jk}⟩` for `j, k ∈ [N]`, where the third register holds a `b`-bit string
representing the entry exactly ("we assume the entries of `A` can be represented exactly"): the
entry `A_{jk}` is written as the code `code j k`, which the fixed decoding `dec` reads back as
`A_{jk}`. -/
def IsEntryOracle {N b : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (dec : Qubits b → ℂ)
    (O : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N + b))
      (Qubits (Nat.clog 2 N + Nat.clog 2 N + b)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧
    ∃ code : Fin N → Fin N → Qubits b, (∀ j k, dec (code j k) = A j k) ∧
      ∀ (j k : Fin N) (z : Qubits b),
        act O (ket (Fin.append (Fin.append (natToBits (Nat.clog 2 N) j) (natToBits (Nat.clog 2 N) k))
          z)) =
        ket (Fin.append (Fin.append (natToBits (Nat.clog 2 N) j) (natToBits (Nat.clog 2 N) k))
          (z + code j k))

/-- CKS p.2–3 (Problem 1: "a procedure `P_A` that computes entries of `A` as described in
equations (1) and (2)"): the pair `(Ocol, Oent)` is a sparse-access oracle `P_A` for `A`: the map
(1) and the map (2). A use of `P_A` is a use of either map. -/
def IsSparseAccessOracle {N b : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) (dec : Qubits b → ℂ)
    (Ocol : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N)) (Qubits (Nat.clog 2 N + Nat.clog 2 N)) ℂ)
    (Oent : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N + b))
      (Qubits (Nat.clog 2 N + Nat.clog 2 N + b)) ℂ) : Prop :=
  IsColumnOracle A d Ocol ∧ IsEntryOracle A dec Oent

/-- CKS p.2–3 (Problem 1: "a procedure `P_B` that prepares the state `|b⟩`"): `O` is a unitary on
`n = ⌈log₂ N⌉` qubits with `O|0ⁿ⟩ = |b⟩`. -/
def IsStatePrep {N : ℕ} (bvec : EuclideanSpace ℂ (Fin N))
    (O : Matrix (Qubits (Nat.clog 2 N)) (Qubits (Nat.clog 2 N)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧ act O (zeroKet (Nat.clog 2 N)) = padState (Nat.clog 2 N) (normalizedVec bvec)

/-- The flag wire (wire `0`) of a register laid out as flag, `n` output wires, `m` garbage wires. -/
def flagWire (n m : ℕ) : Fin (1 + n + m) :=
  Fin.castAdd m (Fin.castAdd n (0 : Fin 1))

/-- The output-register part of a basis string of the layout flag / output / garbage. -/
def outPart {n m : ℕ} (z : Qubits (1 + n + m)) : Qubits n :=
  fun i => z (Fin.castAdd m (Fin.natAdd 1 i))

/-- The garbage part of a basis string of the layout flag / output / garbage. -/
def garbagePart {n m : ℕ} (z : Qubits (1 + n + m)) : Qubits m :=
  fun k => z (Fin.natAdd (1 + n) k)

/-- CKS p.3 (Problem 1: "output a state `|x̃⟩` such that `‖|x̃⟩ − |x⟩‖ ≤ ε`, succeeding with
probability `Ω(1)` (say, at least `1/2`), with a flag indicating success"): the final state `φ`
(register laid out as flag wire, `n` output wires, `m` garbage wires) has the flag equal to `1`
with probability `p ≥ 1/2`, and the normalized flag-`1` branch `p^{−1/2} (|1⟩⟨1|_flag ⊗ I) φ` is
within Euclidean distance `ε` of `|1⟩_flag ⊗ |x⟩ ⊗ |g⟩` for some unit garbage state `g` (the
garbage is arbitrary, so a global phase of the output is absorbed into `g`). -/
def QLSPSuccess {n m : ℕ} (φ : EuclideanSpace ℂ (Qubits (1 + n + m))) (x : EuclideanSpace ℂ (Qubits n))
    (ε : ℝ) : Prop :=
  1 / 2 ≤ probEvent φ (fun z => z (flagWire n m) = true) ∧
    ∃ g : EuclideanSpace ℂ (Qubits m), ‖g‖ = 1 ∧
      ‖(WithLp.toLp 2 fun z => if z (flagWire n m) = true then
            ((Real.sqrt (probEvent φ fun z => z (flagWire n m) = true))⁻¹ : ℂ) * φ z else 0 :
          EuclideanSpace ℂ (Qubits (1 + n + m))) -
        WithLp.toLp 2 fun z => if z (flagWire n m) = true then x (outPart z) * g (garbagePart z)
          else 0‖ ≤ ε

/-! ### Sanity tests -/

/-- The identity is `1`-sparse. -/
example : IsSparse (1 : Matrix (Fin 3) (Fin 3) ℂ) 1 := by
  constructor <;> intro j <;> refine Finset.card_le_one.2 fun a ha b hb => ?_ <;>
    simp [Matrix.one_apply] at ha hb <;> subst ha <;> subst hb <;> rfl

/-- `|b⟩` is a unit vector for `b ≠ 0`. -/
example {ι : Type*} [Fintype ι] (b : EuclideanSpace ℂ ι) (hb : b ≠ 0) : ‖normalizedVec b‖ = 1 := by
  rw [normalizedVec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (norm_nonneg b))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hb)

/-- Padding a vector on `N = 2ⁿ` indices loses nothing: the basis vector `e_0` becomes `|0ⁿ⟩`. -/
example : padState 1 (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (fun _ => false) = 1 := by
  simp [padState, bitsToNat]

end QAlgorithms
