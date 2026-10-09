import Mathlib

/-!
# Registers, states, measurement (shared definition layer)

Sources: R. de Wolf, *Quantum Computing: Lecture Notes* (PDF pages cited as "de Wolf p.N"),
and A. Childs, *Lecture Notes on Quantum Algorithms* ("Childs p.N").

Conventions fixed once here and used by every statement of the run:

* An `n`-qubit register has computational-basis index set `Qubits n = Fin n → Bool`. Wire
  `i : Fin n` is the source's qubit `i + 1`; wire `0` is the most significant bit
  (de Wolf p.44: `|k⟩ = |k₁ … kₙ⟩`, `k₁` most significant).
* States are vectors of `EuclideanSpace ℂ ι`; being a state (unit norm) is the predicate
  `IsState`, carried as a hypothesis wherever the source says "state" (trap Q1).
* Operators are matrices `Matrix ι ι ℂ`; unitaries are members of `Matrix.unitaryGroup ι ℂ`;
  the tensor product of operators is `Matrix.kronecker` (`A ⊗ₖ B` acts on `ι × κ`, `A` on the
  first factor). A product index `ι × κ` is a two-register state space, first factor = first
  register.
* The amplitude `⟨i|ψ⟩` is `inner ℂ (ket i) ψ` (Mathlib's inner product is conjugate-linear in
  its first argument), which equals the coordinate `ψ i`.
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- de Wolf p.26 (§2.1), p.44 (§4.5); Childs p.9 (§1.2). The computational-basis index set of an
`n`-qubit register: bit strings `Fin n → Bool`. Wire `i` is the source's qubit `i + 1`, and wire
`0` is the most significant bit (see `bitsToNat`). -/
abbrev Qubits (n : ℕ) := Fin n → Bool

/-- de Wolf p.44 (§4.5): the integer `k = k₁ … kₙ` written by an `n`-bit string, most significant
bit first: wire `i` carries the weight `2^(n-1-i)`. (The subtraction is exact since `i < n`.)
Mathlib's `finFunctionFinEquiv` is little-endian, the opposite convention, and is not used
directly. -/
def bitsToNat {n : ℕ} (b : Qubits n) : ℕ :=
  ∑ i : Fin n, if b i then 2 ^ (n - 1 - (i : ℕ)) else 0

/-- de Wolf p.44 (§4.5): the bijection `{0,1}ⁿ ≃ {0, …, 2ⁿ - 1}` whose forward map is
`bitsToNat` (most significant bit first; see `bitsEquivFin_apply`). Built from Mathlib's
little-endian `finFunctionFinEquiv` by reversing the wire order. -/
def bitsEquivFin (n : ℕ) : Qubits n ≃ Fin (2 ^ n) :=
  ((Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin n)) finTwoEquiv.symm)).trans
    finFunctionFinEquiv

/-- de Wolf p.44 (§4.5): the `n`-bit most-significant-bit-first expansion of `k mod 2ⁿ`
(the inverse of `bitsToNat` on `{0, …, 2ⁿ - 1}`). -/
def natToBits (n k : ℕ) : Qubits n :=
  (bitsEquivFin n).symm ⟨k % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- de Wolf p.26 (§2.1): the computational basis state `|i⟩`. -/
noncomputable def ket {ι : Type*} [DecidableEq ι] (i : ι) : EuclideanSpace ℂ ι :=
  EuclideanSpace.single i 1

/-- de Wolf p.30 (§2.4.1): the `n`-qubit zero state `|0ⁿ⟩`. -/
noncomputable def zeroKet (n : ℕ) : EuclideanSpace ℂ (Qubits n) :=
  ket (fun _ : Fin n => false)

/-- de Wolf p.26 (§2.1), Childs p.9 (§1.1): `ψ` is a (pure) quantum state, i.e. a unit vector.
Every "state" hypothesis of a statement is `IsState` (trap Q1). -/
def IsState {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) : Prop :=
  ‖ψ‖ = 1

/-- de Wolf p.26 (§2.1): the vector `A ψ` obtained by applying the operator (matrix) `A` to `ψ`
(matrix–vector product, repackaged as a vector of `EuclideanSpace`). -/
noncomputable def act {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp ψ))

/-- de Wolf p.26 (§2.1), p.170 (§18.1): the tensor product `ψ ⊗ φ` of a state of the first
register and a state of the second, `(ψ ⊗ φ)(i, j) = ψ(i) φ(j)`. -/
noncomputable def tensorVec {ι κ : Type*} (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun p => ψ p.1 * φ p.2)

/-- de Wolf p.26 (§2.1), p.36 (§3.2): the probability `|⟨z|ψ⟩|²` of outcome `z` when the state
`ψ` is measured in the computational basis (meaningful for `IsState ψ`). -/
noncomputable def prob {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    ℝ :=
  ‖inner ℂ (ket z) ψ‖ ^ 2

/-- de Wolf p.111 (§12.1), Childs p.106 (§21.2): the probability that a computational-basis
measurement of the whole register gives an outcome satisfying `P` (for instance: a designated
output qubit reads `b`, or the outcome lies in an accepting set). -/
noncomputable def probEvent {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι)
    (P : ι → Prop) [DecidablePred P] : ℝ :=
  ∑ z ∈ Finset.univ.filter P, prob ψ z

/-- de Wolf p.36 (§3.2): the probability that measuring only the first register of a
two-register state gives `a` (equivalently: measure both registers and discard the second
outcome). -/
noncomputable def marginalFst {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ψ : EuclideanSpace ℂ (ι × κ)) (a : ι) : ℝ :=
  ∑ b : κ, prob ψ (a, b)

/-- Childs p.15 (Lemma 2.2): the ordered product `U_t ⋯ U_2 U_1` of `t` operators, where the
source's `U_1` is `U 0` and acts first; the empty product (`t = 0`) is the identity. -/
def orderedProd {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} (U : Fin t → Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (List.ofFn U).reverse.prod

/-- Childs p.10 (§1.3, (1.4)), de Wolf p.47 (§4 exercise 4), p.112 (§12.1): the spectral
(operator) norm `‖A‖ = max_{‖v‖ = 1} ‖A v‖`, the largest singular value. Defined as the norm of
Mathlib's L2-operator norm structure on matrices (`Matrix.instL2OpNormedAddCommGroup`, a scoped
instance), named here so that statements never pick up another matrix norm by accident. -/
noncomputable def specNorm {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : ℝ :=
  @Norm.norm (Matrix m n 𝕜) (Matrix.instL2OpNormedAddCommGroup).toNorm A

/-- Childs p.118 (§23.2): the Frobenius norm `‖X‖_F = (Σ_{a,b} |X_{ab}|²)^{1/2}`, the norm of
Mathlib's (scoped) `Matrix.frobeniusNormedAddCommGroup`. -/
noncomputable def frobNorm {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) : ℝ :=
  @Norm.norm (Matrix m n ℂ) (Matrix.frobeniusNormedAddCommGroup).toNorm X

/-- de Wolf p.65 (§7.1), Childs p.107 (§21.3): the Hamming weight `|x|`, the number of positions
where `x` is `1` (for a search input: the number of solutions). -/
def hammingWeight {ι : Type*} [Fintype ι] (x : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

/-- de Wolf p.26 (§2.1, (2.1)), p.35 (§3.1): the inner product `i · j = Σ_k i_k j_k mod 2` of two
bit strings, as a bit. The sum is in `Bool` with Mathlib's Boolean-ring structure (`+` is xor,
`*` is and). Bitwise xor `i ⊕ j` of bit strings is the addition `i + j` of the Pi group
`Fin n → Bool`. -/
def dotBits {n : ℕ} (i j : Qubits n) : Bool :=
  ∑ k : Fin n, (i k && j k)

/-! ### Sanity tests -/

theorem bitsEquivFin_apply {n : ℕ} (b : Qubits n) : (bitsEquivFin n b : ℕ) = bitsToNat b := by
  simp only [bitsEquivFin, Equiv.trans_apply, finFunctionFinEquiv_apply, Equiv.arrowCongr_apply,
    bitsToNat]
  refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin n)) _ _ (fun i => ?_)
  simp only [Function.comp_apply, Equiv.symm_symm, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hi := i.isLt
  have e1 : n - 1 - (n - ((i : ℕ) + 1)) = i := by omega
  cases h : b (Fin.rev i) <;> simp [finTwoEquiv, Fin.val_rev, e1, h]

example : bitsToNat (![true, false] : Qubits 2) = 2 := by decide

example : bitsToNat (![false, true, true] : Qubits 3) = 3 := by decide

example : dotBits (![true, true] : Qubits 2) ![true, true] = false := by decide

example : dotBits (![true, false] : Qubits 2) ![true, true] = true := by decide

example : hammingWeight (![true, false, true] : Fin 3 → Bool) = 2 := by decide

example {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : IsState (ket i) := by
  simp [IsState, ket]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (ψ : EuclideanSpace ℂ ι) :
    inner ℂ (ket i) ψ = ψ i := by
  simp [ket, EuclideanSpace.inner_single_left]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (i z : ι) :
    prob (ket i) z = if z = i then 1 else 0 := by
  by_cases h : z = i <;> simp [prob, ket, h, EuclideanSpace.inner_single_left, Pi.single_apply]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  simp [act]

/-- A unitary preserves the norm of every vector, hence maps states to states. -/
theorem act_norm_of_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    ‖act U ψ‖ = ‖ψ‖ := by
  have h : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U ∈ unitary (EuclideanSpace ℂ ι →L[ℂ]
      EuclideanSpace ℂ ι) := Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) hU
  have e : act U ψ = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U ψ := rfl
  rw [e]
  exact ContinuousLinearMap.norm_map_of_mem_unitary h ψ

example (U : Fin 0 → Matrix (Fin 2) (Fin 2) ℂ) : orderedProd U = 1 := by
  simp [orderedProd]

example (U : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) : orderedProd U = U 1 * U 0 := by
  simp [orderedProd, List.ofFn_succ]

end QAlgorithms
