import QAlgorithms.Defs.LearningHardInstances

/-!
# Superoperators, quantum channels in Kraus form, the erasure channel, achievable rates
(shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N", and D. Gottesman, *Stabilizer
codes and quantum error correction* (PhD thesis, 1997), cited "Gottesman thesis p.N" (PDF pages).

A superoperator is a plain function on matrices (`Superop ι κ`); a quantum operation in the
sources' sense (intro eq. (23), p.4–5: "ρ → Σ_i E_i ρ E_i†, where the E_i s are normalized so
Σ E_i† E_i = I") is a superoperator with a finite normalized Kraus family (`IsChannel`). Equality
of superoperators is equality on every operator, hence (by linearity) on every input state,
superpositions and parts of entangled states included.
-/

namespace QAlgorithms

open scoped ComplexConjugate Matrix

/-- Gottesman intro p.5, eq. (23), and p.20 (§4.2): a superoperator, i.e. a map from operators on
the space indexed by `ι` to operators on the space indexed by `κ`. Unbundled: linearity is
supplied by `IsChannel` or by construction. -/
abbrev Superop (ι κ : Type*) := Matrix ι ι ℂ → Matrix κ κ ℂ

/-- Gottesman intro p.5, eq. (23) (thesis p.90, §7.5): the Kraus operators `E j : κ × ι` are
normalized, `Σ_j E_j† E_j = I`. -/
def IsKrausFamily {K ι κ : Type*} [Fintype K] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) : Prop :=
  ∑ j, (E j)ᴴ * E j = 1

/-- Gottesman intro p.5, eq. (23): the map `ρ ↦ Σ_j E_j ρ E_j†`. -/
noncomputable def krausApply {K ι κ : Type*} [Fintype K] [Fintype ι]
    (E : K → Matrix κ ι ℂ) : Superop ι κ :=
  fun ρ => ∑ j, E j * ρ * (E j)ᴴ

/-- Gottesman intro pp.4–5, eq. (23) (thesis p.90): `Φ` is a quantum operation ("the most
general quantum operation, including decoherence"): it is given by some finite normalized Kraus
family. In finite dimension these are exactly the trace-preserving completely positive maps. -/
def IsChannel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (Φ : Superop ι κ) : Prop :=
  ∃ (m : ℕ) (E : Fin m → Matrix κ ι ℂ), IsKrausFamily E ∧ ∀ ρ, Φ ρ = krausApply E ρ

/-- Gottesman intro p.19 (Def. 1) and p.37 (the *-decoder): the single-Kraus map
`ρ ↦ A ρ A†` (a unitary gate, an isometry, a projector such as an r-filter). -/
def conjSuperop {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) : Superop ι κ :=
  fun ρ => A * ρ * Aᴴ

/-- Gottesman intro p.21 (Def. 4) and p.35 (Def. 8): the tensor product
`Φ_0 ⊗ ⋯ ⊗ Φ_{k−1}` of superoperators acting on `k` registers (a separate filter, decoder or EC
on each block), defined on every operator through the matrix-unit expansion
`X = Σ_{x,x'} X_{x x'} ⊗_i |x_i⟩⟨x'_i|`, so entangled inputs are included. -/
noncomputable def piSuperop {ι κ : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι κ) : Superop (Fin k → ι) (Fin k → κ) :=
  fun X => Matrix.of fun y y' =>
    ∑ x : Fin k → ι, ∑ x' : Fin k → ι,
      X x x' * ∏ i, Φ i (Matrix.single (x i) (x' i) 1) (y i) (y' i)

/-- Gottesman thesis p.90 (§7.4–7.5, the 1-EPP picture): `id_R ⊗ Φ`, with the reference `R` the
first factor: `Φ` is applied to every block `X_{a a'} = (X_{(a,i),(a',i')})_{i,i'}`. -/
def idTensorSuperop {R ι κ : Type*} (Φ : Superop ι κ) : Superop (R × ι) (R × κ) :=
  fun X => Matrix.of fun p q => Φ (Matrix.of fun i i' => X (p.1, i) (q.1, i')) p.2 q.2

/-- Overwrite the registers in the range of `w` of the configuration `y` by `z` (helper for
`liftSuperop`). -/
noncomputable def overwrite {α : Type*} {k N : ℕ} (w : Fin k ↪ Fin N) (y : Fin N → α)
    (z : Fin k → α) : Fin N → α :=
  open Classical in
  fun a => if h : ∃ i, w i = a then z h.choose else y a

/-- Gottesman intro p.18 (§4.1: "an error that can affect all of the qubits involved in the
action") and p.40 (Def. 12): the superoperator `Ψ`, acting on the `k` registers in the range of
`w` together with an extra factor `E` (the environment), lifted to `N` registers, the identity on
the registers outside the range of `w`. Entry `((y, e), (y', e'))` is `Ψ` applied to the block of
`X` with the outside configurations of `y` and `y'` held fixed, evaluated at the inside
configurations `y ∘ w`, `y' ∘ w`; this is `id_outside ⊗ Ψ` (off-diagonal outside blocks are kept,
as for any superoperator that is the identity on a factor). -/
noncomputable def liftSuperop {α E : Type*} {k N : ℕ} (w : Fin k ↪ Fin N)
    (Ψ : Superop ((Fin k → α) × E) ((Fin k → α) × E)) :
    Superop ((Fin N → α) × E) ((Fin N → α) × E) :=
  fun X => Matrix.of fun p q =>
    Ψ (Matrix.of fun a b => X (overwrite w p.1 a.1, a.2) (overwrite w q.1 b.1, b.2))
      (p.1 ∘ w, p.2) (q.1 ∘ w, q.2)

/-- Gottesman thesis pp.89–90 (§7.4–7.5): `k` EPR pairs, the maximally entangled state
`|Φ_k⟩ = 2^{−k/2} Σ_{x ∈ {0,1}^k} |x⟩|x⟩` on `Qubits k × Qubits k`, reference register first. -/
noncomputable def maxEntangled (k : ℕ) : EuclideanSpace ℂ (Qubits k × Qubits k) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then ((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℂ) else 0

/-- Gottesman thesis pp.89–90 (§7.4: a 1-EPP succeeds when Bob's pairs are good EPR pairs): the
entanglement fidelity `⟨Φ_k| (id ⊗ Φ)(|Φ_k⟩⟨Φ_k|) |Φ_k⟩` of a superoperator `Φ` on `k` qubits
(real part; it is real for a channel). -/
noncomputable def entanglementFidelity {k : ℕ} (Φ : Superop (Qubits k) (Qubits k)) : ℝ :=
  (∑ a, ∑ b, conj (maxEntangled k a) *
    (idTensorSuperop (R := Qubits k) Φ (pureDensity (maxEntangled k))) a b *
      maxEntangled k b).re

/-- Gottesman thesis p.90 (§7.5): the Kraus operators of the qubit erasure channel with erasure
probability `p` and an erasure flag (output `(qubit, flag)`). Index `0` is `√(1−p) |ψ⟩ ↦ |ψ⟩|0⟩`;
indices `1, …, 4` are `√(p/2) |a⟩|1⟩⟨c|` for `(a, c) = (0,0), (0,1), (1,0), (1,1)`. The channel is
`ρ ↦ (1 − p) ρ ⊗ |0⟩⟨0| + p Tr(ρ) (I/2) ⊗ |1⟩⟨1|`: with probability `p` the qubit is replaced by
the maximally mixed state ("totally randomized") and the receiver learns which qubit it was.
Normalized for `0 ≤ p ≤ 1`, the source's range (a hypothesis of the statements). -/
noncomputable def erasureKraus (p : ℝ) : Fin 5 → Matrix (Bool × Bool) Bool ℂ :=
  let flip : Bool → Bool → Matrix (Bool × Bool) Bool ℂ := fun a c =>
    Matrix.of fun o b => if o = (a, true) ∧ b = c then (Real.sqrt (p / 2) : ℂ) else 0
  ![Matrix.of fun o b => if o = (b, false) then (Real.sqrt (1 - p) : ℂ) else 0,
    flip false false, flip false true, flip true false, flip true true]

/-- Gottesman thesis p.90 (§7.5): the erasure channel applied independently to each of `n`
qubits, with product Kraus operators; output register `q` holds `(qubit q, flag q)`. -/
noncomputable def erasureChannel (n : ℕ) (p : ℝ) : Superop (Qubits n) (Fin n → Bool × Bool) :=
  krausApply fun j : Fin n → Fin 5 => Matrix.of fun y z => ∏ q, erasureKraus p (j q) (y q) (z q)

/-- Gottesman thesis p.80 (§7.1: capacity in the limit of infinitely many qubits sent, rate
`k/n`), p.89 (§7.4: quantum codes = 1-EPPs, success = good EPR pairs) and p.91 (§7.5): `R` is an
achievable rate of unassisted quantum communication over the family `Nch n` of `n`-use channels:
for every `ε, δ > 0`, for all large `n` there are `k ≥ (R − δ) n` and an encoding channel and a
decoding channel (arbitrary quantum operations; no back communication) with entanglement fidelity
at least `1 − ε`. The capacity is the supremum of the achievable rates; statements give it as a
two-sided threshold. -/
def IsAchievableQRate {Out : ℕ → Type*} [∀ n, Fintype (Out n)] [∀ n, DecidableEq (Out n)]
    (Nch : (n : ℕ) → Superop (Qubits n) (Out n)) (R : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k : ℕ, (R - δ) * n ≤ k ∧
    ∃ Enc : Superop (Qubits k) (Qubits n), IsChannel Enc ∧
      ∃ Dec : Superop (Out n) (Qubits k), IsChannel Dec ∧
        1 - ε ≤ entanglementFidelity (Dec ∘ Nch n ∘ Enc)

/-! ### Sanity tests -/

example {ι : Type*} [Fintype ι] [DecidableEq ι] : IsChannel (fun ρ : Matrix ι ι ℂ => ρ) :=
  ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

example {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    conjSuperop A ρ = krausApply (fun _ : Fin 1 => A) ρ := by
  simp [conjSuperop, krausApply]

example {R ι : Type*} (X : Matrix (R × ι) (R × ι) ℂ) :
    idTensorSuperop (R := R) (fun ρ : Matrix ι ι ℂ => ρ) X = X := by
  ext p q; rfl

example : maxEntangled 0 (fun _ => false, fun _ => false) = 1 := by
  simp [maxEntangled]

example (k : ℕ) (x : Qubits k) :
    maxEntangled k (x, x) = ((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℂ) := by
  simp [maxEntangled]

example : erasureKraus 0 0 (true, false) true = 1 ∧ erasureKraus 0 1 (false, true) false = 0 := by
  simp [erasureKraus]

theorem erasureKraus_isKraus {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsKrausFamily (erasureKraus p) := by
  have ha : ((Real.sqrt (1 - p) : ℂ)) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hb : ((Real.sqrt (p / 2) : ℂ)) * (Real.sqrt (p / 2) : ℂ) = ((p / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  ext b c
  simp only [IsKrausFamily, Fin.sum_univ_five, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_bool, erasureKraus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.of_apply]
  have hp2 : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h0]
  have h22 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have key : ((Real.sqrt p : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
      (((Real.sqrt p : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = (p : ℂ) / 2 := by
    rw [div_mul_div_comm, ← sq, ← sq, hp2, h22]
  cases b <;> cases c <;> simp [Matrix.one_apply, Complex.conj_ofReal, ha, hb] <;>
    rw [key] <;> ring

end QAlgorithms
