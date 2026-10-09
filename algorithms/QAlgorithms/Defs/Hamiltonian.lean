import QAlgorithms.Defs.CompressedOracle

/-!
# Hamiltonians, spectral gaps, adiabatic evolution, quantum signal processing
(shared definition layer)

Hermiticity is Mathlib's `Matrix.IsHermitian`; it is a hypothesis of the statements (or part of
`HasSimpleGroundState`). Eigenvalues are counted with multiplicity and sorted increasingly.
-/

namespace QAlgorithms

/-- Childs p.162 (§30.3), p.182 (Lemma 33.1), de Wolf p.129 (§14.2): the eigenvalues of a Hermitian
matrix, counted with multiplicity, in increasing order (Mathlib's `IsHermitian.eigenvalues₀` is
decreasing; it is composed with `Fin.rev`). For a non-Hermitian matrix the value is `0`
(statements assume `IsHermitian`). -/
noncomputable def ascEigenvalues {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : Fin (Fintype.card ι) → ℝ :=
  open Classical in
  if h : A.IsHermitian then fun k => h.eigenvalues₀ (Fin.rev k) else 0

/-- Childs p.160 (§30.1, "the instantaneous ground state energy" `E(s)`), p.182, de Wolf p.129:
the smallest eigenvalue `λ_min(A)` of a Hermitian matrix (`0` on the empty index type, which
statements exclude). -/
noncomputable def minEigenvalue {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : ℝ :=
  if h : 0 < Fintype.card ι then ascEigenvalues A ⟨0, h⟩ else 0

/-- Childs p.162 (§30.2: "the gap between the smallest eigenvalue `E(s)` of `H(s)` and the nearest
distinct eigenvalue"), p.166 (§31.2: "the gap between the ground and first excited states"),
p.182 (Lemma 33.1): the second smallest minus the smallest eigenvalue, counted with multiplicity
(so a degenerate ground level has gap `0`); `0` if there are fewer than two eigenvalues. Under
`HasSimpleGroundState` it is the source's gap. -/
noncomputable def spectralGap {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : ℝ :=
  if h : 2 ≤ Fintype.card ι then ascEigenvalues A ⟨1, h⟩ - ascEigenvalues A ⟨0, by omega⟩ else 0

/-- Childs p.160 (§30.1: "the ground state of `H(s)` is nondegenerate"): `A` is Hermitian, acts on a
space of dimension at least two, and its smallest eigenvalue is simple. -/
def HasSimpleGroundState {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : Prop :=
  A.IsHermitian ∧ 2 ≤ Fintype.card ι ∧ 0 < spectralGap A

/-- Childs p.160 ((30.6)): `φ` is a ground state of `A`: a unit vector with `A φ = λ_min(A) φ`. -/
def IsGroundState {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (φ : EuclideanSpace ℂ ι) : Prop :=
  IsState φ ∧ act A φ = (minEigenvalue A : ℂ) • φ

/-- Childs p.159–160 ((30.5)): `ψ` solves the Schrödinger equation in rescaled time,
`i dψ/ds = T H(s) ψ(s)` for `s ∈ [0, 1]` (one-sided derivatives at the endpoints), i.e.
`dψ/ds = −i T H(s) ψ(s)` (sign convention `e^{−iHt}`, (30.2); trap Q12). The derivatives
`Ḣ(s), Ḧ(s)` of the statements are `derivWithin` on `[0, 1]`. -/
def SolvesScaledSchrodinger {ι : Type*} [Fintype ι] (H : ℝ → Matrix ι ι ℂ) (T : ℝ)
    (ψ : ℝ → EuclideanSpace ℂ ι) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt ψ (-Complex.I • (T : ℂ) • act (H s) (ψ s)) (Set.Icc 0 1) s

/-- Childs p.165 ((31.2)): the problem Hamiltonian `H_P = Σ_z h(z) |z⟩⟨z|`. -/
def problemHamiltonian {n : ℕ} (h : Qubits n → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun z => (h z : ℂ)

/-- Childs p.165–166 ((31.3) with `f(s) = s`), p.181 ((33.13)): the linear interpolation
`H(s) = (1 − s) H_B + s H_P`. -/
def linInterp {ι : Type*} (HB HP : Matrix ι ι ℂ) (s : ℝ) : Matrix ι ι ℂ :=
  ((1 - s : ℝ) : ℂ) • HB + (s : ℂ) • HP

/-- Childs p.166 ((31.8)): `∆_min = min_{s ∈ [0,1]} ∆(s)`, as the infimum of the gaps over `[0, 1]`
(a nonempty set of nonnegative reals, so the infimum is not a junk value; it is attained when
`H` is continuous). -/
noncomputable def minGap {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ℝ → Matrix ι ι ℂ) : ℝ :=
  sInf ((fun s => spectralGap (H s)) '' Set.Icc 0 1)

/-- Childs p.181 ((33.14)–(33.16)): the restriction of `(1 − s) H_B + s H_C` to the computational
subspace `span{|ψ_0⟩, …, |ψ_k⟩}`: entry `(0, 0)` is `s − 1`, the entries `(j, j + 1)` and
`(j + 1, j)` are `−s`, all others are `0`. -/
def clockPathMatrix (k : ℕ) (s : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then s - 1
    else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -s else 0

/-- Childs p.152 ((29.6)): the signal rotation `W(x) = [[x, i√(1 − x²)], [i√(1 − x²), x]]`
(for the source's `x ∈ [−1, 1]`). -/
noncomputable def qspW (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ); Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)]

/-- Childs p.152 ((29.7)): the `z` rotation `e^{iϕσ_z} = diag(e^{iϕ}, e^{−iϕ})`. -/
noncomputable def qspZ (ϕ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (ϕ * Complex.I), 0; 0, Complex.exp (-(ϕ * Complex.I))]

/-- Childs p.152 ((29.7)): `W_Φ(x) = e^{iϕ_0σ_z} W(x) e^{iϕ_1σ_z} W(x) ⋯ W(x) e^{iϕ_kσ_z}` for
`Φ = (ϕ_0, …, ϕ_k)` (`k` factors `W(x)`). -/
noncomputable def qspSequence {k : ℕ} (Φ : Fin (k + 1) → ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (List.ofFn fun i : Fin (k + 1) => if i = 0 then qspZ (Φ i) else qspW x * qspZ (Φ i)).prod

/-- Childs p.153 (Lemma 29.1: "an even function has parity 0 and an odd function has parity 1"):
`P` has parity `k mod 2`, i.e. `P(−x) = (−1)^k P(x)`. -/
def HasParity (P : Polynomial ℂ) (k : ℕ) : Prop :=
  P.comp (-Polynomial.X) = (-1 : ℂ) ^ k • P

/-! ### Sanity tests -/

example : clockPathMatrix 2 0 = Matrix.diagonal ![-1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [clockPathMatrix]

/-- With `k = 0` (no `W(x)` factors), `W_Φ(x) = e^{iϕ_0σ_z}` (Childs p.152, base case). -/
example (Φ : Fin 1 → ℝ) (x : ℝ) : qspSequence Φ x = qspZ (Φ 0) := by
  simp [qspSequence]

example (Φ : Fin 2 → ℝ) (x : ℝ) : qspSequence Φ x = qspZ (Φ 0) * (qspW x * qspZ (Φ 1)) := by
  simp [qspSequence, List.ofFn_succ]

/-- An even polynomial (here `X²`) has parity `0`. -/
example : HasParity (Polynomial.X ^ 2) 0 := by
  simp [HasParity]

/-- The eigenvalues of `diag(2, 1)` in increasing order are `1, 2`, so its gap is `1`. -/
example : ascEigenvalues (Matrix.diagonal ![(2 : ℂ), 1]) ⟨0, by simp⟩ ≤
    ascEigenvalues (Matrix.diagonal ![(2 : ℂ), 1]) ⟨1, by simp⟩ := by
  have h : (Matrix.diagonal ![(2 : ℂ), 1]).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i; fin_cases i <;> simp
  simp only [ascEigenvalues, dif_pos h]
  exact h.eigenvalues₀_antitone (Fin.rev_le_rev.2 (by simp [Fin.le_def]))

example {n : ℕ} (h : Qubits n → ℝ) : (problemHamiltonian h).IsHermitian := by
  rw [problemHamiltonian, Matrix.isHermitian_diagonal_iff]
  intro z; simp [IsSelfAdjoint]

end QAlgorithms
