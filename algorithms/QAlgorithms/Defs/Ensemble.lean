import QAlgorithms.Defs.Adiabatic

/-!
# POVMs, tensor powers, state identification, von Neumann entropy (shared definition layer)

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N" (PDF pages), and S. Arunachalam, R. de Wolf, *A survey of quantum learning
theory* (2017), cited "survey p.N" (PDF pages).

Conventions: a measurement with finite outcome set `O` is a family of positive semidefinite
matrices summing to the identity (`IsPOVM`); outcome `o` on a density matrix `ρ` has probability
`Re Tr(M_o ρ)` (frozen `effectProb`), and a pure state `ψ` enters as `pureDensity ψ = |ψ⟩⟨ψ|`.
Matrix functions of Hermitian matrices are Mathlib's continuous functional calculus `cfc` (a real
function applied to the eigenvalues; every function is continuous on the finite spectrum).
-/

namespace QAlgorithms

open scoped ComplexConjugate ComplexOrder

/-- Survey p.3 (§2.1), Arunachalam p.159 (§7.3.2): an `O`-outcome POVM on the space indexed by
`ι` is a family `{M_o}_{o ∈ O}` of positive semidefinite matrices with `∑_o M_o = I`. -/
def IsPOVM {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (M : O → Matrix ι ι ℂ) : Prop :=
  (∀ o, (M o).PosSemidef) ∧ ∑ o, M o = 1

/-- Survey p.3 and p.7 (§3.2), Arunachalam p.128 (§6.3.2): the probability that measuring the
density matrix `ρ` with the POVM `M` gives an outcome in the event `P`,
`∑_{o ∈ P} Tr(M_o ρ)` (real part, frozen `effectProb`). -/
noncomputable def povmEventProb {O ι : Type*} [Fintype O] [Fintype ι] (M : O → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) (P : O → Prop) [DecidablePred P] : ℝ :=
  ∑ o ∈ Finset.univ.filter P, effectProb (M o) ρ

/-- Arunachalam p.163 (§7.4.1), survey pp.13–14 (§4.2): the `T`-fold tensor power
`|ψ⟩^{⊗T}` of a vector `ψ` indexed by `ι`, as the vector indexed by `Fin T → ι` (copy `i` is the
`i`-th factor) with coordinates `z ↦ ∏_i ψ(z_i)`. At `T = 0` it is the unit vector of the
one-point space. -/
noncomputable def tensorPow {ι : Type*} (T : ℕ) (ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin T → ι) :=
  WithLp.toLp 2 fun z => ∏ i, ψ (z i)

/-- Arunachalam p.159 (§7.3.2), survey p.5 (§2.3): the average success probability
`P_M(E) = ∑_i p_i ⟨ψ_i|M_i|ψ_i⟩` of the POVM `M` (indexed by the same finite set `O` as the
ensemble) in identifying the states of the ensemble `E = {(p_i, |ψ_i⟩)}_{i ∈ O}`. -/
noncomputable def ensembleSuccess {O ι : Type*} [Fintype O] [Fintype ι] (p : O → ℝ)
    (ψ : O → EuclideanSpace ℂ ι) (M : O → Matrix ι ι ℂ) : ℝ :=
  ∑ i, p i * effectProb (M i) (pureDensity (ψ i))

/-- Arunachalam p.159 (§7.3.2), survey p.5 (§2.3): `P^opt(E) = max_M P_M(E)`, the optimal
average success probability over all `|O|`-outcome POVMs `M`. The set of values is bounded
(each `⟨ψ_i|M_i|ψ_i⟩ ∈ [0, ‖ψ_i‖²]`), and nonempty whenever `O` is nonempty (put `I` on one
outcome); the junk value `0` occurs only for an empty ensemble, which `∑ p_i = 1` excludes. -/
noncomputable def optSuccess {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (p : O → ℝ)
    (ψ : O → EuclideanSpace ℂ ι) : ℝ :=
  ⨆ M : {M : O → Matrix ι ι ℂ // IsPOVM M}, ensembleSuccess p ψ M.1

/-- Arunachalam p.159 (§7.3.2): the success probability of the pretty good measurement,
`P^PGM(E) = ∑_i p_i |⟨ν_i|ψ_i⟩|²`, where `ψ'_i = √p_i ψ_i`, `ρ = ∑_i |ψ'_i⟩⟨ψ'_i|` and
`ν_i = ρ^{−1/2} ψ'_i`, the inverse square root taken over the non-zero eigenvalues of `ρ`
(here `cfc (x ↦ (√x)⁻¹) ρ`, which sends the eigenvalue `0` to `0` since `(√0)⁻¹ = 0` in Lean).
The PGM's operators are `|ν_i⟩⟨ν_i|`. -/
noncomputable def pgmSuccess {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (p : O → ℝ)
    (ψ : O → EuclideanSpace ℂ ι) : ℝ :=
  let ψ' : O → EuclideanSpace ℂ ι := fun i => (Real.sqrt (p i) : ℂ) • ψ i
  let ρ : Matrix ι ι ℂ := ∑ i, pureDensity (ψ' i)
  ∑ i, p i * ‖inner ℂ (act (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ) (ψ' i)) (ψ i)‖ ^ 2

/-- Arunachalam p.159 (§7.3.1): the von Neumann entropy in bits, `S(ρ) = −Tr(ρ log ρ)` with
`log` to base 2 (so that the uniform distribution on `{0,1}^d` has entropy `d`, p.156), computed
as `−Re Tr(f(ρ))` for `f(x) = x log₂ x` (`0 log 0 = 0`, since `Real.logb 2 0 = 0`). Junk: `cfc`
returns `0` on a non-Hermitian argument; statements carry `IsDensityMatrix`. -/
noncomputable def vnEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.logb 2 x) ρ).trace.re

/-! ### Sanity tests -/

example : IsPOVM (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
  ⟨fun _ => Matrix.PosSemidef.one, by simp⟩

example {ι : Type*} (ψ : EuclideanSpace ℂ ι) (z : Fin 0 → ι) : tensorPow 0 ψ z = 1 := by
  simp [tensorPow]

example {ι : Type*} (ψ : EuclideanSpace ℂ ι) (z : Fin 1 → ι) : tensorPow 1 ψ z = ψ (z 0) := by
  simp [tensorPow]

theorem povmEventProb_true {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    {M : O → Matrix ι ι ℂ} (hM : IsPOVM M) {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    povmEventProb M ρ (fun _ => True) = 1 := by
  have h : ∑ o, effectProb (M o) ρ = ((∑ o, M o) * ρ).trace.re := by
    simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [povmEventProb, Finset.filter_true, h, hM.2, one_mul, hρ.2, Complex.one_re]

example {O ι : Type*} [Fintype O] [Fintype ι] (p : O → ℝ) (ψ : O → EuclideanSpace ℂ ι) :
    ensembleSuccess p ψ 0 = 0 := by
  simp [ensembleSuccess, effectProb]

example {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (ψ : O → EuclideanSpace ℂ ι) :
    pgmSuccess 0 ψ = 0 := by
  simp [pgmSuccess]

example {ι : Type*} [Fintype ι] [DecidableEq ι] : vnEntropy (1 : Matrix ι ι ℂ) = 0 := by
  simp [vnEntropy, cfc_one]

end QAlgorithms
