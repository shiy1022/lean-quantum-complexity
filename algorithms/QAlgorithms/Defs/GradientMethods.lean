import QAlgorithms.Defs.AmplitudeEstimation

/-!
# Gradient algorithms, function oracles, subgradients, amplitude encoding, gate sets
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 1, 4, 5 and 7. A collection of `d` registers of `q` qubits each is indexed by
`Fin d → Qubits q` (register `i` is the source's register `i + 1`); binary strings are read as
integers most significant bit first (`bitsToNat`).
-/

namespace QAlgorithms

/-- Nannicini p.106, Def. 5.1 and the binary oracle below it:
`U_F |x_1⟩ ⋯ |x_d⟩ |y⟩ = |x_1⟩ ⋯ |x_d⟩ |y ⊞ F(x)⟩`, where `⊞` is addition modulo `2^q` of the
integers represented (most significant bit first) by the `q`-bit output register. `F` takes
integer (here natural-number) values, reduced modulo `2^q` by `natToBits`. A permutation matrix;
column `r` is the image of `|r⟩`. (Not the frozen `xorOracle`, which adds bitwise.) -/
def modAddOracle (d q : ℕ) (F : (Fin d → Qubits q) → ℕ) :
    Matrix ((Fin d → Qubits q) × Qubits q) ((Fin d → Qubits q) × Qubits q) ℂ :=
  Matrix.of fun p r => if p.1 = r.1 ∧ p.2 = natToBits q (bitsToNat r.2 + F r.1) then 1 else 0

/-- Nannicini p.107 (§5.1.1) and p.110 (Alg. 3): the operator `M ⊗ ⋯ ⊗ M` acting with the same
matrix `M` on each of `d` registers (register `i` = index `i`), entry `∏_i M_{x_i, y_i}`. -/
def piKron {ι : Type*} (d : ℕ) (M : Matrix ι ι ℂ) : Matrix (Fin d → ι) (Fin d → ι) ℂ :=
  Matrix.of fun x y => ∏ i, M (x i) (y i)

/-- Nannicini p.108, Fig. 5.1 (and pp.107–108): the state before measurement of Jordan's gradient
circuit: start in `|0⟩_q^{⊗d} ⊗ |1⃗⟩_q`, apply `H^{⊗q}` to each of the `d` input registers and the
QFT `Q_q` (frozen `qftQubits`) to the output register, apply the binary oracle `U_F` once, then
`Q_q†` to each input register. -/
noncomputable def jordanGradientState (d q : ℕ) (F : (Fin d → Qubits q) → ℕ) :
    EuclideanSpace ℂ ((Fin d → Qubits q) × Qubits q) :=
  act (Matrix.kronecker (piKron d (star (qftQubits q))) (1 : Matrix (Qubits q) (Qubits q) ℂ))
    (act (modAddOracle d q F)
      (tensorVec (act (piKron d (hadamardN q)) (ket fun _ _ => false))
        (act (qftQubits q) (ket fun _ => true))))

/-- Nannicini p.109, §5.1.1: the point `ĵ = j/2^q − 1/2 + 1/2^{q+1}` of the symmetric grid
`G_q ⊂ [−1/2, 1/2]` represented by the `q`-bit string `j`. -/
noncomputable def gridPoint (q : ℕ) (j : Qubits q) : ℝ :=
  (bitsToNat j : ℝ) * ((2 : ℝ) ^ q)⁻¹ - 2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹

/-- Nannicini p.109, §5.1.1: the Fourier transform on the grid `G_q`,
`Q_{G_q} |k⟩ = 2^{−q/2} Σ_j e^{2πi 2^q ĵ k̂} |j⟩` (column `k` is the image of `|k⟩`). -/
noncomputable def gridQFT (q : ℕ) : Matrix (Qubits q) (Qubits q) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (gridPoint q j : ℂ) * (gridPoint q k : ℂ)) *
      ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)

/-- Nannicini p.110, Alg. 3 (with the phase oracle of Def. 5.10 as used there): the state before
measurement of the gradient algorithm: `d` registers of `q` qubits in `|0⟩`, `H^{⊗q}` on each,
the phase oracle `U_f |x⟩ = e^{2πi 2^q f(x̂)} |x⟩` (`x̂` the grid point of `x`), then `Q_{G_q}†` on
each register. The outcome `k_j` of register `j` gives `g̃_j = gridPoint q k_j`. -/
noncomputable def gradientAlgState (d q : ℕ) (f : (Fin d → ℝ) → ℝ) :
    EuclideanSpace ℂ (Fin d → Qubits q) :=
  act (piKron d (star (gridQFT q)))
    (act (Matrix.diagonal fun x : Fin d → Qubits q =>
        Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (f fun i => gridPoint q (x i) : ℂ)))
      (act (piKron d (hadamardN q)) (ket fun _ _ => false)))

/-- Nannicini p.112, Def. 5.9: `W` is a probability oracle for `f : X → [0, 1]`: `W` is unitary,
`f` takes values in `[0, 1]`, and for every `x`,
`W |0⟩|0⃗⟩|x⟩ = √f(x) |1⟩|ψ_x^{(1)}⟩ + √(1 − f(x)) |0⟩|ψ_x^{(0)}⟩` for some states `ψ_x^{(0)},
ψ_x^{(1)}`. Register order: the flag qubit first, then the work register (whose `|0⃗⟩` is `z0`)
together with the `x` register. -/
def IsProbabilityOracle {κ X : Type*} [Fintype κ] [DecidableEq κ] [Fintype X] [DecidableEq X]
    (z0 : κ) (W : Matrix (Bool × (κ × X)) (Bool × (κ × X)) ℂ) (f : X → ℝ) : Prop :=
  W ∈ Matrix.unitaryGroup (Bool × (κ × X)) ℂ ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    ∀ x, ∃ ψ0 ψ1 : EuclideanSpace ℂ (κ × X), IsState ψ0 ∧ IsState ψ1 ∧
      act W (ket (false, (z0, x))) =
        (Real.sqrt (f x) : ℂ) • tensorVec (ket true) ψ1 +
          (Real.sqrt (1 - f x) : ℂ) • tensorVec (ket false) ψ0

/-- Nannicini p.115, Fig. 5.3: the Hadamard-test circuit on a flag qubit (first), a work register
of `n` qubits and an `x` register: in time order `H`, `X` on the flag, controlled-`U` on the work
register, `X`, controlled-`V` on work and `x` registers, `H`, `X`. Since `U` is sandwiched between
`X` gates it acts when the original flag is `|0⟩`; `V` acts when it is `|1⟩`. One controlled-`U`,
one controlled-`V` and five single-qubit gates. -/
noncomputable def hadamardTestCircuit {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Qubits n) (Qubits n) ℂ) (V : Matrix (Qubits n × X) (Qubits n × X) ℂ) :
    Matrix (Bool × (Qubits n × X)) (Bool × (Qubits n × X)) ℂ :=
  let Hf := Matrix.kronecker hadamard (1 : Matrix (Qubits n × X) (Qubits n × X) ℂ)
  let Xf := Matrix.kronecker pauliX (1 : Matrix (Qubits n × X) (Qubits n × X) ℂ)
  Xf * Hf * controlled V * Xf * controlled (Matrix.kronecker U (1 : Matrix X X ℂ)) * Xf * Hf

/-- Nannicini p.120, Def. 5.24 (and p.181, Rem. 8.6): `g ∈ V*` is an `ε`-subgradient of `f` at
`x̄` over the domain `D`: `f(x) ≥ f(x̄) + ⟨g, x − x̄⟩ − ε` for every `x ∈ D` (`ε = 0` is a
subgradient). The pairing `⟨g, x⟩` is the linear functional `g` applied to `x`. -/
def IsEpsSubgradOn {E : Type*} [AddCommGroup E] [Module ℝ E] (D : Set E) (f : E → ℝ) (ε : ℝ)
    (xbar : E) (g : Module.Dual ℝ E) : Prop :=
  ∀ x ∈ D, f xbar + g (x - xbar) - ε ≤ f x

/-- Nannicini p.181, §8.1: the trace inner product `⟨G, X⟩ = Tr(G X†)` as a real-linear functional
on matrices (real part; it is real when `G` and `X` are Hermitian). -/
noncomputable def traceRePairing {ι : Type*} [Fintype ι] (G : Matrix ι ι ℂ) :
    Module.Dual ℝ (Matrix ι ι ℂ) where
  toFun X := (G * X.conjTranspose).trace.re
  map_add' X Y := by
    simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' r X := by
    simp [Matrix.conjTranspose_smul, Matrix.trace_smul]

/-- Nannicini p.121, Def. 5.26: the central finite-difference gradient approximation
`∇^{(η)} f(x)_j = (f(x + η e_j) − f(x − η e_j)) / (2η)`. Junk value `0` at `η = 0`; the source
has `η > 0`, a hypothesis of the statements. -/
noncomputable def fdGradient {d : ℕ} (η : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun j => (f (x + η • Pi.single j 1) - f (x - η • Pi.single j 1)) * (2 * η)⁻¹

/-- Nannicini p.121, Def. 5.27: the finite-difference Laplace approximation
`Δ^{(η)} f(x) = Σ_j (f(x + η e_j) − 2 f(x) + f(x − η e_j)) / η²`. Junk value `0` at `η = 0`. -/
noncomputable def fdLaplacian {d : ℕ} (η : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j, (f (x + η • Pi.single j 1) - 2 * f x + f (x - η • Pi.single j 1)) * (η ^ 2)⁻¹

/-- Nannicini p.119, Def. 5.20 (`p = 1`): the closed `ℓ₁` ball `B_1(x, r) = {y : ‖x − y‖₁ ≤ r}`.
The `ℓ_∞` ball is Mathlib's `Metric.closedBall` (the sup norm is the norm of `Fin d → ℝ`). -/
def ballL1 {d : ℕ} (x : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {y | ∑ i, |x i - y i| ≤ r}

/-- Nannicini p.90, Def. 4.26: the rotation `R_Y(θ) = [[cos θ/2, −sin θ/2], [sin θ/2, cos θ/2]]`,
indexed by `Bool` (`false` = `|0⟩` = row/column 0). -/
noncomputable def rotY (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => match a, b with
    | false, false => (Real.cos (θ / 2) : ℂ)
    | false, true => -(Real.sin (θ / 2) : ℂ)
    | true, false => (Real.sin (θ / 2) : ℂ)
    | true, true => (Real.cos (θ / 2) : ℂ)

/-- Nannicini p.124 (§5.2) and p.125 (Fig. 5.6): the value `N(k, j)` of node `(k, j)` (level `k`,
position `j`, both 0-based) of the binary tree built from `x ∈ ℝ^{2^n}`: the sum of `x_i²` over the
`j`-th block of `2^{n−k}` consecutive indices. `N(0, 0) = ‖x‖²`, `N(n, i) = x_i²`. -/
noncomputable def ampTreeValue (n : ℕ) (x : Fin (2 ^ n) → ℝ) (k j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ n) => (i : ℕ) / 2 ^ (n - k) = j), x i ^ 2

/-- Nannicini p.126, Alg. 4: the integer value `j` (most significant bit first) of the first `k`
wires of `z`. -/
def prefixVal {n : ℕ} (z : Qubits n) (k : ℕ) : ℕ :=
  ∑ i : Fin n, if (i : ℕ) < k ∧ z i = true then 2 ^ (k - 1 - (i : ℕ)) else 0

/-- Nannicini p.126, Alg. 4, lines 2 and 5: the rotation angle
`2 arccos √(N(k+1, 2j) / (N(k+1, 2j) + N(k+1, 2j+1)))` used on wire `k` (0-based) when the first
`k` wires hold the value `j` (`k = 0` is line 2). A zero denominator gives the junk angle `π`; that
branch has amplitude `√N(k, j) = 0`, so it does not affect the state. -/
noncomputable def alg4Angle (n : ℕ) (x : Fin (2 ^ n) → ℝ) (k j : ℕ) : ℝ :=
  2 * Real.arccos (Real.sqrt (ampTreeValue n x (k + 1) (2 * j) *
    (ampTreeValue n x (k + 1) (2 * j) + ampTreeValue n x (k + 1) (2 * j + 1))⁻¹))

/-- Nannicini p.126, Alg. 4, line 5: the controlled rotation `Σ_j |j⟩⟨j| ⊗ R_Y(angle k j)` with
the first `k` wires as control and wire `k` as target, acting as the identity on the later wires:
entry `(y, z)` is `R_Y(angle k j)_{y_k, z_k}` if `y` and `z` agree off wire `k` (with `j` the value
of the first `k` wires), else `0`. -/
noncomputable def alg4Step (n : ℕ) (x : Fin (2 ^ n) → ℝ) (k : Fin n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z =>
    if ∀ a, a ≠ k → y a = z a then rotY (alg4Angle n x k (prefixVal z k)) (y k) (z k) else 0

/-- Nannicini p.124 (§5.2) and p.126 (Alg. 4): the `n`-qubit circuit returned by Alg. 4, in time
order: the rotations `alg4Step n x k` for `k = 0, …, n − 1` (the source appends wire `k` in `|0⟩`
just before step `k`; here all `n` wires are present from the start, the later ones still in
`|0⟩`), then the sign diagonal `Σ_j sign(x_j) |j⟩⟨j|` of line 7, with sign `+1` at `x_j = 0` so
that it is unitary. -/
noncomputable def alg4Unitary (n : ℕ) (x : Fin (2 ^ n) → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal (fun z => if x (bitsEquivFin n z) < 0 then -1 else 1) * orderedProd (alg4Step n x)

/-- Nannicini p.28, Thm. 1.43: the universal gate set `{H, T, CX}` in which gates are counted. -/
def htcxGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 gateT, Gate.ofMatrix2 cnot}

/-- Nannicini p.172 (Lem. 7.39) and p.173 (Prop. 7.41): "two-qubit gates", i.e. arbitrary unitary
gates acting on two qubits. -/
def twoQubitGateSet : Set Gate :=
  {g | g.arity = 2 ∧ g.IsUnitary}

/-! ### Sanity tests -/

theorem natToBits_bitsToNat {q : ℕ} (z : Qubits q) : natToBits q (bitsToNat z) = z := by
  have h := (bitsEquivFin q z).isLt
  rw [bitsEquivFin_apply] at h
  unfold natToBits
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [bitsEquivFin_apply, Nat.mod_eq_of_lt h]

example (d q : ℕ) : modAddOracle d q (fun _ => 0) = 1 := by
  ext p r
  by_cases h : p = r
  · subst h; simp [modAddOracle, natToBits_bitsToNat]
  · simp only [modAddOracle, Matrix.of_apply, add_zero, natToBits_bitsToNat, Matrix.one_apply, h,
      if_false]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (Prod.ext h1 h2)

example {ι : Type*} [DecidableEq ι] (d : ℕ) : piKron d (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp [piKron, Matrix.one_apply, Finset.prod_boole, funext_iff]

example : gridPoint 1 ![false] = -(1 / 4) ∧ gridPoint 1 ![true] = 1 / 4 := by
  constructor <;> norm_num [gridPoint, bitsToNat]

example {d : ℕ} (η c : ℝ) (x : Fin d → ℝ) : fdGradient η (fun _ => c) x = 0 := by
  funext j; simp [fdGradient]

example {E : Type*} [AddCommGroup E] [Module ℝ E] (c : ℝ) (x : E) :
    IsEpsSubgradOn Set.univ (fun _ => c) 0 x 0 := by
  intro y _; simp

example : rotY 0 = 1 := by
  ext a b; cases a <;> cases b <;> simp [rotY]

example (n : ℕ) (x : Fin (2 ^ n) → ℝ) : ampTreeValue n x 0 0 = ∑ i, x i ^ 2 := by
  rw [ampTreeValue, Finset.filter_true_of_mem]
  intro i _
  simpa using Nat.div_eq_of_lt i.isLt

example : alg4Unitary 0 (fun _ => 1) = 1 := by
  simp [alg4Unitary, orderedProd]
  funext z
  norm_num

end QAlgorithms
