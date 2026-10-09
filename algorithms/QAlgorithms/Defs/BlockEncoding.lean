import QAlgorithms.Defs.GradientMethods

/-!
# Clock Hamiltonian, iterative refinement, block-encodings, state-preparation pairs
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 6–7. The source's 1-based indices `1, …, N` are `Fin N` (0-based). A
block-encoding puts the auxiliary register **first** (Def. 7.11: `(⟨0|_a ⊗ I) U (|0⟩_a ⊗ I)`).
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- Nannicini p.135, §6.1.1: the clock Hamiltonian `H_B` in the basis `|u^{(1)}⟩, …, |u^{(N)}⟩`,
the symmetric tridiagonal `N × N` matrix with zero diagonal and
`(H_B)_{j,j+1} = (H_B)_{j+1,j} = ½ √(j(N − j))` for `j = 1, …, N − 1` (1-based); here 0-based,
entry `(i, i+1)` is `½ √((i + 1)(N − i − 1))` (the subtraction is in `ℕ` and never truncates, as
`i + 1 < N`). -/
noncomputable def clockHamiltonian (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then
      ((2⁻¹ * Real.sqrt (((min (i : ℕ) j + 1) * (N - min (i : ℕ) j - 1) : ℕ) : ℝ) : ℝ) : ℂ)
    else 0

/-- Nannicini p.136, §6.1.1: the mirror matrix `M_s = Σ_j |u^{(j)}⟩⟨u^{(N+1−j)}|`, which sends the
`j`-th basis vector to the `(N + 1 − j)`-th; 0-based, `i ↦ N − 1 − i` (`Fin.rev`). An eigenvector
`ψ` of `H_B` is symmetric iff `M_s ψ = ψ`, antisymmetric iff `M_s ψ = −ψ`. -/
def mirrorMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if i = Fin.rev j then 1 else 0

/-- Nannicini p.158, Alg. 5: the iterates of iterative refinement for `Ax = b`:
`x^{(0)} = 0` and `x^{(k)} = x^{(k−1)} + ‖r^{(k−1)}‖ x̂^{(k)}` with the residual
`r^{(k−1)} = b − A x^{(k−1)}`, where `xhat k` is the solver output `x̂^{(k)}` used at iteration
`k ≥ 1` (`xhat 0` is never read). -/
noncomputable def iterRefineX {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N))
    (xhat : ℕ → EuclideanSpace ℂ (Fin N)) : ℕ → EuclideanSpace ℂ (Fin N)
  | 0 => 0
  | k + 1 => iterRefineX A b xhat k + (‖b - act A (iterRefineX A b xhat k)‖ : ℂ) • xhat (k + 1)

/-- Nannicini p.159, Defs. 7.10–7.11: `U` is an `(α, a, ξ)`-block-encoding of `A`: `U` is unitary
and `‖α (⟨0⃗|_a ⊗ I) U (|0⃗⟩_a ⊗ I) − A‖ ≤ ξ` in the operator norm (frozen `specNorm`), the
auxiliary register (index type `κ`, all-zero element `z0`) first. The source's form is
`κ = Qubits a`, `z0 = 0`; a composite auxiliary register uses its all-zero element. -/
def IsBlockEncoding {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] (z0 : κ)
    (U : Matrix (κ × ι) (κ × ι) ℂ) (α ξ : ℝ) (A : Matrix ι ι ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (κ × ι) ℂ ∧
    specNorm ((α : ℂ) • (Matrix.of fun i j => U (z0, i) (z0, j)) - A) ≤ ξ

/-- Nannicini p.161, Def. 7.16: `(P_L, P_R)` is a `(β, p, ξ)`-state-preparation pair for
`y ∈ ℂ^m` (0-based): `P_L, P_R` are `p`-qubit unitaries, `‖y‖₁ ≤ β`, and with
`P_L|0⟩ = Σ_j c_j|j⟩`, `P_R|0⟩ = Σ_j d_j|j⟩` (index `j` ↔ the integer `bitsToNat j`),
`Σ_{j=0}^{m−1} |β c_j^† d_j − y_j| ≤ ξ` and `c_j^† d_j = 0` for `j = m, …, 2^p − 1`. The
definition also records `m ≤ 2^p`, implicit in the source (the coefficients `c_j, d_j` exist only
for `j < 2^p`). -/
def IsStatePrepPair {m p : ℕ} (β ξ : ℝ) (y : Fin m → ℂ) (PL PR : Matrix (Qubits p) (Qubits p) ℂ) :
    Prop :=
  PL ∈ Matrix.unitaryGroup (Qubits p) ℂ ∧ PR ∈ Matrix.unitaryGroup (Qubits p) ℂ ∧ m ≤ 2 ^ p ∧
    ∑ j, ‖y j‖ ≤ β ∧
    ∑ j : Fin m, ‖(β : ℂ) * conj (act PL (zeroKet p) (natToBits p j)) *
        act PR (zeroKet p) (natToBits p j) - y j‖ ≤ ξ ∧
    ∀ j : Qubits p, m ≤ bitsToNat j → conj (act PL (zeroKet p) j) * act PR (zeroKet p) j = 0

/-! ### Sanity tests -/

example : clockHamiltonian 2 0 1 = 2⁻¹ ∧ clockHamiltonian 2 1 0 = 2⁻¹ ∧
    clockHamiltonian 2 0 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [clockHamiltonian]

example : mirrorMatrix 2 0 1 = 1 ∧ mirrorMatrix 2 0 0 = 0 := by
  constructor <;> simp [mirrorMatrix] <;> decide

example {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N))
    (xhat : ℕ → EuclideanSpace ℂ (Fin N)) : iterRefineX A b xhat 1 = (‖b‖ : ℂ) • xhat 1 := by
  simp [iterRefineX, act]

example {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] (z0 : κ) :
    IsBlockEncoding z0 (1 : Matrix (κ × ι) (κ × ι) ℂ) 1 0 1 := by
  refine ⟨one_mem _, ?_⟩
  have h : ((1 : ℝ) : ℂ) • (Matrix.of fun i j : ι => (1 : Matrix (κ × ι) (κ × ι) ℂ) (z0, i) (z0, j)) -
      1 = 0 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [h, specNorm]
  letI : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  exact le_of_eq norm_zero

end QAlgorithms
