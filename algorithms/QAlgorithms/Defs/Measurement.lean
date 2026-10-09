import QAlgorithms.Defs.Stabilizer

/-!
# Basis states, product states, sequential measurement, mixed states (shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapter 1.

Conventions are the frozen ones of `QAlgorithms.Defs.Basic`: an `n`-qubit register is indexed by
`Qubits n = Fin n → Bool`, wire `i` is the source's qubit `i + 1`, and the first qubit is the most
significant bit (Nannicini p.14: "the first qubit corresponds to the most significant bit").
Two-register objects put register `A` first.
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- Nannicini p.13, Def. 1.16: a state `ψ` is a *basis state* if `ψ = α_k |k⟩` for some basis
index `k` and some `α_k ∈ ℂ` with `|α_k|² = 1`; otherwise it is a superposition. Generic in the
index type, so that it applies to a `q`-qubit register (`Qubits q`) and to a single qubit
(`Bool`). A basis state is automatically a unit vector. -/
def IsBasisState {ι : Type*} [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) : Prop :=
  ∃ (k : ι) (α : ℂ), ‖α‖ = 1 ∧ ψ = α • ket k

/-- Nannicini pp.14–15, §1.2.1: the tensor product `|φ_1⟩ ⊗ ⋯ ⊗ |φ_q⟩` of `q` single-qubit
vectors, with amplitude `∏_k φ_k(j_k)` on the basis string `j`; wire `i` carries the source's
qubit `i + 1` (the first qubit is the most significant one, as for `bitsToNat`). -/
noncomputable def prodState {q : ℕ} (φ : Fin q → EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ (Qubits q) :=
  WithLp.toLp 2 fun z => ∏ i, φ i (z i)

/-- Nannicini p.19, Postulate 3: the state after a measurement gate on wire `k` of the
`q`-qubit state `ψ = Σ_j α_j |j⟩` returns `x`, namely
`Σ_{j : j_k = x} α_j / √(Σ_{ℓ : ℓ_k = x} |α_ℓ|²) |j⟩`. The outcome probability
`Σ_{j : j_k = x} |α_j|²` is the frozen `probEvent ψ (fun j => j k = x)`.
Junk value: when that probability is `0` the inverse square root is `0` and the result is the zero
vector; such an outcome has probability `0`, so every product that uses it carries weight `0`. -/
noncomputable def collapseQubit {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (k : Fin q) (x : Bool) :
    EuclideanSpace ℂ (Qubits q) :=
  ((Real.sqrt (probEvent ψ fun j => j k = x))⁻¹ : ℂ) •
    WithLp.toLp 2 fun j => if j k = x then ψ j else 0

/-- Nannicini pp.19–20, Postulate 3 and Prop. 1.27: the probability that measuring the wires of the
list `l` one at a time, in list order (head first), each measurement followed by the Postulate 3
collapse, returns the bit `y k` on every measured wire `k`. Values of `y` off `l` are ignored.
`seqMeasProb ψ [] y = 1` and
`seqMeasProb ψ (k :: l) y = Pr_ψ(Q_k = y_k) · seqMeasProb (collapse of ψ) l y`. -/
noncomputable def seqMeasProb {q : ℕ} : EuclideanSpace ℂ (Qubits q) → List (Fin q) → Qubits q → ℝ
  | _, [], _ => 1
  | ψ, k :: l, y => probEvent ψ (fun j => j k = y k) * seqMeasProb (collapseQubit ψ k (y k)) l y

/-- Nannicini p.31, Def. 1.47: the total variation distance `d_TV(P, Q) = ½ Σ_j |p_j − q_j|` of two
discrete distributions on the same finite sample space, given by their probability vectors. -/
noncomputable def tvDist {ι : Type*} [Fintype ι] (P Q : ι → ℝ) : ℝ :=
  2⁻¹ * ∑ j, |P j - Q j|

/-- Nannicini pp.37–38, Defs. 1.62 and 1.64: the partial trace `Tr_B` over the **second**
register `B` of a two-register operator, `(Tr_B M)_{jk} = Σ_h M_{(j,h),(k,h)}` (the linear
extension of `Tr_B(|j⟩⟨k| ⊗ |h⟩⟨ℓ|) = |j⟩⟨k| ⟨ℓ|h⟩`). The reduced density matrix of register `A`
is `ρ^(A) = traceRight ρ^(AB)`. (The frozen `traceLeft` traces out the first register.) -/
def traceRight {α β : Type*} [Fintype β] (M : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  Matrix.of fun j k => ∑ h, M (j, h) (k, h)

/-- Nannicini p.35, Def. 1.55: the density matrix `ρ = Σ_{j=1}^m p_j |ψ_j⟩⟨ψ_j|` of the ensemble
`{p_j, |ψ_j⟩}` (0-based here). The ensemble conditions (`p_j ≥ 0`, `Σ p_j = 1`, each `ψ_j` a unit
vector) are hypotheses of the statements that use it. -/
noncomputable def ensembleDensity {ι : Type*} {m : ℕ} (p : Fin m → ℝ)
    (ψ : Fin m → EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  ∑ j, (p j : ℂ) • pureDensity (ψ j)

/-- Nannicini p.14 (§1.2.1) and p.172 (Lem. 7.39): a register of `a + b` qubits viewed as two
registers, the first `a` wires forming the first register:
`z ↦ (z_1 … z_a, z_{a+1} … z_{a+b})`, inverse `Fin.append` (as in the frozen `inputState`). -/
def qubitsAppendEquiv (a b : ℕ) : Qubits (a + b) ≃ Qubits a × Qubits b where
  toFun z := (fun i => z (Fin.castAdd b i), fun j => z (Fin.natAdd a j))
  invFun p := Fin.append p.1 p.2
  left_inv z := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    simp

/-- Nannicini p.35 (§1.4) and p.174 (Rem. 7.42): the density matrix `ρ ⊗ |0^w⟩⟨0^w|` on `q + w`
qubits, one copy of the `q`-qubit state `ρ` on the first `q` wires and `w` ancillas in `|0⟩` on
the last `w` wires. -/
def withZeroAncillas {q : ℕ} (ρ : Matrix (Qubits q) (Qubits q) ℂ) (w : ℕ) :
    Matrix (Qubits (q + w)) (Qubits (q + w)) ℂ :=
  Matrix.of fun y z =>
    if (qubitsAppendEquiv q w y).2 = (fun _ => false) ∧ (qubitsAppendEquiv q w z).2 = (fun _ => false)
    then ρ (qubitsAppendEquiv q w y).1 (qubitsAppendEquiv q w z).1 else 0

/-- Nannicini p.35, Rem. 1.59: the probability `⟨z|σ|z⟩` of the outcome `z` when every qubit of a
register in the mixed state `σ` is measured (the real part of the diagonal entry, which is real for
a density matrix). A circuit `W` maps `ρ` to `W ρ W†` (§1.4). -/
noncomputable def densityProb {ι : Type*} (σ : Matrix ι ι ℂ) (z : ι) : ℝ :=
  (σ z z).re

/-- Nannicini p.173 (Prop. 7.41) and p.174 (Rem. 7.42): the expected value `Σ_z ⟨z|σ|z⟩ Y(z)` of
the classical output `Y(z)` computed from a final measurement of a register in the state `σ`. -/
noncomputable def densityMean {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) (Y : ι → ℝ) : ℝ :=
  ∑ z, densityProb σ z * Y z

/-- Nannicini p.173, Prop. 7.41: the variance `Σ_z ⟨z|σ|z⟩ (Y(z) − E[Y])²` of that output; the
source's standard deviation is its square root. -/
noncomputable def densityVariance {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) (Y : ι → ℝ) : ℝ :=
  ∑ z, densityProb σ z * (Y z - densityMean σ Y) ^ 2

/-! ### Sanity tests -/

example {ι : Type*} [DecidableEq ι] (i : ι) : IsBasisState (ket i) :=
  ⟨i, 1, by simp, by simp⟩

example (q : ℕ) : prodState (fun _ : Fin q => ket false) = zeroKet q := by
  ext z
  simp only [prodState, zeroKet, ket]
  by_cases h : z = fun _ => false
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ false := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    rw [EuclideanSpace.single_apply, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [EuclideanSpace.single_apply, hi])

example {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (k : Fin q) (y : Qubits q) :
    seqMeasProb ψ [k] y = probEvent ψ (fun j => j k = y k) := by
  simp [seqMeasProb]

example {ι : Type*} [Fintype ι] (P : ι → ℝ) : tvDist P P = 0 := by
  simp [tvDist]

example {α β : Type*} [Fintype β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    traceRight (Matrix.kronecker A B) = B.trace • A := by
  ext j k
  simp [traceRight, Matrix.kronecker, Matrix.trace, Finset.mul_sum, mul_comm]

example {ι : Type*} (ψ : EuclideanSpace ℂ ι) :
    ensembleDensity (fun _ : Fin 1 => (1 : ℝ)) (fun _ => ψ) = pureDensity ψ := by
  simp [ensembleDensity]

example {q w : ℕ} (ρ : Matrix (Qubits q) (Qubits q) ℂ) (y z : Qubits q) :
    withZeroAncillas ρ w (Fin.append y fun _ => false) (Fin.append z fun _ => false) = ρ y z := by
  simp [withZeroAncillas, qubitsAppendEquiv]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    densityProb (pureDensity ψ) z = prob ψ z := by
  simp [densityProb, pureDensity, prob, ket, EuclideanSpace.inner_single_left, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

example {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) : densityMean σ (fun _ => 0) = 0 := by
  simp [densityMean]

end QAlgorithms
