import QAlgorithms.Defs.Basic

/-!
# Elementary gates (shared definition layer)

Single-qubit gates are matrices indexed by `Bool` (`false` is `|0⟩`, row/column 0); two-qubit
gates are indexed by `Bool × Bool` with the first factor the first qubit (the control, for
controlled gates).
-/

namespace QAlgorithms

/-- de Wolf p.26 (§2.1), p.41 (§4.1): the Hadamard gate `H = (1/√2) [[1, 1], [1, -1]]`. -/
noncomputable def hadamard : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a && b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

/-- de Wolf p.26 (§2.1, (2.1)), Childs p.133 (§26.1, (26.2)): the `n`-fold Hadamard transform
`H^{⊗n}`, with `H^{⊗n} |i⟩ = 2^{-n/2} Σ_j (-1)^{i·j} |j⟩`; its `(j, i)` entry is
`2^{-n/2} (-1)^{i·j}`, written `(1/√2)ⁿ (-1)^{i·j}`. -/
noncomputable def hadamardN (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun j i =>
    if dotBits i j then -(((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)

/-- de Wolf p.185 (§20.1), Childs p.152 (§29.1): the Pauli matrix `X = [[0, 1], [1, 0]]`
(bit flip). `pauliY` and `pauliZ` are defined next to it. -/
def pauliX : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then 0 else 1

/-- de Wolf p.185 (§20.1): the Pauli matrix `Y = [[0, -i], [i, 0]]`. -/
def pauliY : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then 0 else if a then Complex.I else -Complex.I

/-- de Wolf p.185 (§20.1), Childs p.152 (§29.1): the Pauli matrix `Z = diag(1, -1)`
(phase flip). -/
def pauliZ : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then -1 else 1

/-- de Wolf p.186 (§20.2): the phase gate `S = diag(1, i)`. -/
def phaseS : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.I else 1

/-- de Wolf p.121 (§13.1), p.186 (§20.2): the `T` gate `diag(1, e^{iπ/4})`. -/
noncomputable def gateT : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.exp (Complex.I * Real.pi / 4) else 1

/-- de Wolf p.26 (§2.1): the controlled-NOT gate `|c, t⟩ ↦ |c, t ⊕ c⟩`, control = first qubit. -/
def cnot : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = xor q.2 q.1 then 1 else 0

/-- de Wolf p.32 (exercise 2.3), p.45 (§4.5): the SWAP gate `|a, b⟩ ↦ |b, a⟩`. -/
def swapGate : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p = (q.2, q.1) then 1 else 0

/-- de Wolf p.44 (§4.5): `R_s = diag(1, e^{2πi/2^s})` (sign `+`, as printed). -/
noncomputable def rotR (s : ℕ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ s) else 1

/-- de Wolf p.44 (§4.5), p.46 (§4.6): the controlled version `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` of an
operator `U`, the control being the first factor: `|c⟩|ψ⟩ ↦ |c⟩ U^c |ψ⟩`. -/
def controlled {κ : Type*} [DecidableEq κ] (U : Matrix κ κ ℂ) : Matrix (Bool × κ) (Bool × κ) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 then U p.2 q.2 else (1 : Matrix κ κ ℂ) p.2 q.2)
    else 0

/-- de Wolf p.65 (§7.2): the reflection `2|z⟩⟨z| - I`, which leaves `|z⟩` fixed and puts `-1` in
front of every other basis state. De Wolf's `R_0` on `n` qubits is `reflAt (fun _ => false)`. -/
def reflAt {ι : Type*} [DecidableEq ι] (z : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if i = z then 1 else -1

/-! ### Sanity tests -/

theorem hadamard_mul_self : hadamard * hadamard = 1 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  ext a b
  cases a <;> cases b <;>
    simp [hadamard, Matrix.mul_apply, Fintype.sum_bool, ← two_mul] <;>
    field_simp <;> simp [h2]

/-- `H^{⊗n}` is real and symmetric, hence self-adjoint (de Wolf p.26: "Hadamard happens to be its
own inverse"). -/
theorem hadamardN_star (n : ℕ) : star (hadamardN n) = hadamardN n := by
  ext i j
  have h : dotBits j i = dotBits i j := by simp only [dotBits, Bool.and_comm]
  simp only [Matrix.star_apply, hadamardN, Matrix.of_apply, h]
  split_ifs <;> simp [Complex.conj_ofReal]

example : hadamardN 0 = 1 := by
  ext i j
  have : i = j := Subsingleton.elim _ _
  subst this
  simp [hadamardN, dotBits]

/-- `H^{⊗1}` is the Hadamard gate, under `{0,1}¹ ≃ {0,1}`. -/
example (i j : Qubits 1) : hadamardN 1 j i = hadamard (j 0) (i 0) := by
  simp only [hadamardN, hadamard, dotBits, Matrix.of_apply, Fin.sum_univ_one, pow_one]
  cases i 0 <;> cases j 0 <;> simp

example : pauliX * pauliX = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply, Fintype.sum_bool]

example : pauliZ * pauliZ = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliZ]

example : phaseS * phaseS = pauliZ := by
  ext a b; cases a <;> cases b <;> simp [phaseS, pauliZ]

example : rotR 1 = pauliZ := by
  ext a b
  cases a <;> cases b <;> simp [rotR, pauliZ]
  rw [show (2 * Real.pi * Complex.I / 2 : ℂ) = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

example : cnot (true, false) (true, true) = 1 ∧ cnot (false, true) (false, true) = 1 := by
  simp [cnot]

example : reflAt (fun _ : Fin 2 => false) (fun _ => false) (fun _ => false) = 1 ∧
    reflAt (fun _ : Fin 2 => false) ![true, false] ![true, false] = -1 := by
  refine ⟨by simp [reflAt], ?_⟩
  have : (![true, false] : Fin 2 → Bool) ≠ fun _ => false := by
    intro h; have := congrFun h 0; simp at this
  simp [reflAt, this]

example {κ : Type*} [DecidableEq κ] : controlled (1 : Matrix κ κ ℂ) = 1 := by
  ext p q
  rcases p with ⟨a, x⟩; rcases q with ⟨b, y⟩
  by_cases h : a = b
  · subst h; cases a <;> simp [controlled, Matrix.one_apply]
  · simp [controlled, h, Matrix.one_apply]

end QAlgorithms
