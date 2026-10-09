import QAlgorithms.Defs.SDP

/-!
# Spectral gaps around a tracked eigenvalue, the adiabatic evolution, QAOA
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapter 9. Nannicini's adiabatic evolution is `dψ/ds = +iT H(s) ψ` (Eq. (9.8)); the
frozen `SolvesScaledSchrodinger` (Childs) has the sign `−i` and is not reused (trap Q12).
-/

namespace QAlgorithms

/-- Nannicini p.211, Defs. 9.8–9.9: the Hermitian matrix `A` has a spectral gap at least `γ`
around `lam`: `A` is Hermitian, `lam` is an eigenvalue of multiplicity one (the frozen
`ascEigenvalues` lists eigenvalues with multiplicity), and every other eigenvalue is at distance
at least `γ` from `lam`. Used pointwise in `s` with `γ` the source's `γ = min_s γ(s)` (a lower
bound on each instantaneous gap); with `γ > 0` it excludes the source's gap-`0` case of
multiplicity `> 1`. -/
def HasGapAround {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam γ : ℝ) : Prop :=
  A.IsHermitian ∧ (∃! k, ascEigenvalues A k = lam) ∧
    ∀ k, ascEigenvalues A k ≠ lam → γ ≤ |ascEigenvalues A k - lam|

/-- Nannicini p.212, Eq. (9.8): `ψ` solves the rescaled adiabatic evolution
`d|ψ(s)⟩/ds = iT H(s) |ψ(s)⟩` on `s ∈ [0, 1]` (sign `+i`, as in the source; derivative within
`[0, 1]`). The initial condition is a separate hypothesis. -/
def SolvesAdiabaticPlus {ι : Type*} [Fintype ι] (H : ℝ → Matrix ι ι ℂ) (T : ℝ)
    (ψ : ℝ → EuclideanSpace ℂ ι) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt ψ (Complex.I • (T : ℂ) • act (H s) (ψ s)) (Set.Icc 0 1) s

/-- Nannicini p.229, Eq. (9.40): the initial QAOA Hamiltonian `H_I = Σ_{j=1}^n σ_j^X`, with
`σ_j^X = I ⊗ ⋯ ⊗ X ⊗ ⋯ ⊗ I` (Pauli `X` on wire `j`, the frozen `CliffordOp.mat` of a Pauli
gate). -/
noncomputable def qaoaMixer (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ j : Fin n, Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli j Stabilizer.Pauli.X)

/-- Nannicini p.230, Eq. (9.42) (with Eq. (9.39), `H_F = Σ_x f(x)|x⟩⟨x|`, the frozen
`problemHamiltonian f`): `U_QAOA(p, β, θ) = e^{−iβ_p H_I} e^{−iθ_p H_F} ⋯ e^{−iβ_1 H_I}
e^{−iθ_1 H_F}`. Layer `k` (the source's `k + 1`) is applied after layers `0, …, k − 1`, and inside
each layer `e^{−iθ H_F}` acts before `e^{−iβ H_I}`. -/
noncomputable def qaoaUnitary {n : ℕ} (f : Qubits n → ℝ) (p : ℕ) (β θ : Fin p → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  orderedProd fun k : Fin p =>
    NormedSpace.exp (-(Complex.I * (β k : ℂ)) • qaoaMixer n) *
      NormedSpace.exp (-(Complex.I * (θ k : ℂ)) • problemHamiltonian f)

/-! ### Sanity tests -/

example {n : ℕ} (f : Qubits n → ℝ) (β θ : Fin 0 → ℝ) : qaoaUnitary f 0 β θ = 1 := by
  simp [qaoaUnitary, orderedProd]

example {ι : Type*} [Fintype ι] (T : ℝ) (ψ : EuclideanSpace ℂ ι) :
    SolvesAdiabaticPlus (fun _ => 0) T (fun _ => ψ) := by
  intro s _
  simpa [act] using hasDerivWithinAt_const s (Set.Icc (0 : ℝ) 1) ψ

example : qaoaMixer 0 = 0 := by
  simp [qaoaMixer]

end QAlgorithms
