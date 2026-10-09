import QAlgorithms.Defs.BlockEncoding

/-!
# Gibbs states, matrix multiplicative weights, semidefinite programs, the MaxCut relaxation
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 7–8. Matrix functions: the exponential is Mathlib's power series
`NormedSpace.exp` (no sign or time factor: the source's `exp(H)`); the logarithm and `x log x` of
Hermitian matrices use Mathlib's continuous functional calculus `cfc` (real functions applied to
the eigenvalues). Iteration indices are the source's, 1-based.
-/

namespace QAlgorithms

open scoped ComplexOrder

/-- Nannicini p.170, Def. 7.34 (and p.183, Alg. 6): the Gibbs state `exp(H) / Tr(exp(H))` of the
Hamiltonian `H`, with the plain matrix exponential. For Hermitian `H` the trace is positive. -/
noncomputable def gibbsState {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (NormedSpace.exp H).trace⁻¹ • NormedSpace.exp H

/-- Nannicini p.182 (Prop. 8.7) and p.183 (Alg. 6): the matrix multiplicative weights iterate
`ρ^{(t)} = exp(−η Σ_{τ=1}^{t−1} G^{(τ)}) / Tr(…)`, i.e. the Gibbs state of `H^{(t)}` with
`H^{(1)} = 0` and `H^{(t+1)} = H^{(t)} − η G^{(t)}`. 1-based: `t ≥ 1` and `G τ` for `τ ≥ 1`
(`G 0` is never read); `mmwuIterate η G 1 = I/n`. -/
noncomputable def mmwuIterate {ι : Type*} [Fintype ι] [DecidableEq ι] (η : ℝ)
    (G : ℕ → Matrix ι ι ℂ) (t : ℕ) : Matrix ι ι ℂ :=
  gibbsState (-(η : ℂ) • ∑ τ ∈ Finset.Ico 1 t, G τ)

/-- Nannicini p.180 (Def. 8.2) and p.182 (§8.1.2): the Bregman divergence of the von Neumann
negative entropy `h(ρ) = Tr(ρ log ρ − ρ)`, the quantum relative entropy
`D_h(ρ‖σ) = Tr(ρ log ρ − ρ log σ − ρ + σ)` (real part). `ρ log ρ` is the functional calculus of
`x ↦ x log x` (`0` at `0`, as `Real.log 0 = 0`). Meaningful for Hermitian `ρ ⪰ 0` and `σ ≻ 0`
(Mathlib's `cfc` is `0` on non-Hermitian input, and `Real.log` is `0` on `x ≤ 0`); every use has a
density matrix `ρ` and a matrix exponential `σ`. -/
noncomputable def qRelEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log σ - ρ + σ).trace.re

/-- Nannicini p.181 (Eq. (8.8)) and p.182 (§8.1.2): `ρ` is a sequence of iterates of mirror
descent over the density matrices `K = S^n_{+,1}` with the mirror map `h` (`∇h = log`,
`(∇h)^{-1} = exp`), step `η` and subgradients `G t`, from `ρ^{(1)} = I/n`:
`ρ^{(t+1)} ∈ argmin_{σ ∈ K} D_h(σ ‖ exp(log ρ^{(t)} − η G^{(t)}))` for every `t ≥ 1` (the argmin
is a membership condition; attainment is part of it). -/
def IsEntropicMirrorDescent {n : ℕ} (η : ℝ) (G : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℕ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ 1 = (n : ℂ)⁻¹ • 1 ∧
    ∀ t ≥ 1, IsDensityMatrix (ρ (t + 1)) ∧
      ∀ σ : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix σ →
        qRelEntropy (ρ (t + 1)) (NormedSpace.exp (cfc Real.log (ρ t) - (η : ℂ) • G t)) ≤
          qRelEntropy σ (NormedSpace.exp (cfc Real.log (ρ t) - (η : ℂ) • G t))

namespace SDP

/-- Nannicini p.178, (P-SDP): `X` is feasible for `max Tr(CX)` s.t. `Tr(A^{(j)} X) ≤ b_j`
(`j = 1, …, m`, here 0-based) and `X ⪰ 0`. The objective `(C * X).trace.re` is written inline. -/
def PrimalFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  X.PosSemidef ∧ ∀ j, (A j * X).trace.re ≤ b j

/-- Nannicini p.178, (D-SDP): `y` is feasible for `min b^⊤ y` s.t.
`Σ_j y_j A^{(j)} − C ⪰ 0` and `y ≥ 0`. The objective `Σ_j b_j y_j` is written inline. -/
def DualFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ (∑ j, (y j : ℂ) • A j - C).PosSemidef

/-- Nannicini p.192, assumption (c): `y` is an optimal solution of (D-SDP): dual feasible with
`b^⊤ y ≤ b^⊤ y'` for every dual feasible `y'`. -/
def IsDualOptimal {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (y : Fin m → ℝ) : Prop :=
  DualFeasible A C y ∧ ∀ y', DualFeasible A C y' → ∑ j, b j * y j ≤ ∑ j, b j * y' j

/-- Nannicini p.188, Def. 8.11, Eq. (8.16): the primal-infeasibility-certificate polytope
`P_ε(X) = {y ∈ ℝ^m : b^⊤ y ≤ γ, Tr((Σ_j y_j A^{(j)} − C) X) ≥ −ε, y ≥ 0}` (real part of the
trace); `ε = 0` is allowed, as used in Prop. 8.19. -/
def picPolytope {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℂ) (γ ε : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : Set (Fin m → ℝ) :=
  {y | ∑ j, b j * y j ≤ γ ∧ ((∑ j, (y j : ℂ) • A j - C) * X).trace.re ≥ -ε ∧ ∀ j, 0 ≤ y j}

/-- Nannicini p.188 (Def. 8.11) and p.189 (Def. 8.13): `O` is a PIC-Oracle_ε of width at most
`w`: on every `X ⪰ 0` (the inputs the source calls it on), it returns "failure" (`none`) iff
`P_ε(X) = ∅`, and every vector `y` it returns lies in `P_ε(X)` and satisfies
`‖Σ_j y_j A^{(j)} − C‖ ≤ w` (operator norm). -/
def IsPICOracle {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℂ) (γ ε w : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
    (O X = none ↔ picPolytope A b C γ ε X = ∅) ∧
      ∀ y, O X = some y → y ∈ picPolytope A b C γ ε X ∧ specNorm (∑ j, (y j : ℂ) • A j - C) ≤ w

/-- Nannicini p.190, Alg. 7, line 7: the loss matrices `M^{(τ)} = (1/w)(Σ_j y^{(τ)}_j A^{(j)} − C)`
built from the oracle answers `ys = [y^{(1)}, …, y^{(t)}]` (1-based: `τ` reads `ys[τ − 1]`). -/
noncomputable def mmwuLoss {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (w : ℝ) (ys : List (Fin m → ℝ)) (τ : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((w : ℂ)⁻¹) • (∑ j, ((ys.getD (τ - 1) 0) j : ℂ) • A j - C)

/-- Nannicini p.190, Alg. 7, lines 2–9: the state of the loop after `k` iterations with step `η`:
either it has stopped with the primal candidate `R ρ^{(t)}` (`inl`) at the first iteration `t`
where the oracle `O` answers "failure", or (`inr`) it holds the answers `[y^{(1)}, …, y^{(k)}]`.
Iteration `t` computes `ρ^{(t)} = mmwuIterate η M t` (`ρ^{(1)} = I/n`) from the losses so far and
queries `O (R ρ^{(t)})`. -/
noncomputable def mmwuRun {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (R η w : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) :
    ℕ → Matrix (Fin n) (Fin n) ℂ ⊕ List (Fin m → ℝ)
  | 0 => Sum.inr []
  | k + 1 =>
      match mmwuRun A C R η w O k with
      | Sum.inl X => Sum.inl X
      | Sum.inr ys =>
          match O ((R : ℂ) • mmwuIterate η (mmwuLoss A C w ys) (k + 1)) with
          | none => Sum.inl ((R : ℂ) • mmwuIterate η (mmwuLoss A C w ys) (k + 1))
          | some y => Sum.inr (ys ++ [y])

/-- Nannicini p.189 (Def. 8.13) and p.190 (Alg. 7): the output of the MMWU algorithm for SDP with
trace bound `R`, tolerance `ε`, width bound `w` and the oracle `O` (the source's
PIC-Oracle_{ε/3}; its specification is a hypothesis of the theorem):
`T = ⌈9 w² R² ln n / ε²⌉`, `η = √(ln n / T)`; run `T` iterations of `mmwuRun`; on a failure return
`inl (R ρ^{(t)})` (the primal candidate, before the rescaling of Lem. 8.12, which the theorem
states), otherwise return `inr ((1/T) Σ_t y^{(t)} + (ε/R) e_1)`, with `e_1` the first coordinate
vector (index `0`; the source's `A^{(1)} = I`). Degenerate case `n = 1`: `T = 0`, no iteration,
and the output is `inr ((ε/R) e_1)`. -/
noncomputable def mmwuSDP {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (R ε w : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) :
    Matrix (Fin n) (Fin n) ℂ ⊕ (Fin m → ℝ) :=
  let T : ℕ := ⌈9 * w ^ 2 * R ^ 2 * Real.log n * (ε ^ 2)⁻¹⌉₊
  let η : ℝ := Real.sqrt (Real.log n * (T : ℝ)⁻¹)
  match mmwuRun A C R η w O T with
  | Sum.inl X => Sum.inl X
  | Sum.inr ys => Sum.inr ((T : ℝ)⁻¹ • ys.sum + (ε * R⁻¹) • fun j : Fin m => if (j : ℕ) = 0 then 1 else 0)

/-- Nannicini p.192, Def. 8.18, Eq. (8.23): the generalized primal-infeasibility-certificate
polytope `P̂(a, c) = {y ∈ ℝ^m : b^⊤ y ≤ γ, Σ_j y_j ≤ r, Σ_j a_j y_j ≥ c, y ≥ 0}`. -/
def genPicPolytope {m : ℕ} (b : Fin m → ℝ) (γ r : ℝ) (a : Fin m → ℝ) (c : ℝ) : Set (Fin m → ℝ) :=
  {y | ∑ j, b j * y j ≤ γ ∧ ∑ j, y j ≤ r ∧ ∑ j, a j * y j ≥ c ∧ ∀ j, 0 ≤ y j}

/-- Nannicini p.199, §8.4.1: the normalized MaxCut cost matrix `Ĉ = C / ‖C‖_F` (frozen
`frobNorm`). Junk value `0` at `C = 0`; statements assume `C ≠ 0`. -/
noncomputable def cHat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((frobNorm C)⁻¹ : ℂ) • C

/-- Nannicini p.200, Eq. (8.26): `f_γ(ρ) = max{γ − Tr(Ĉρ), Σ_j |ρ_jj − 1/n|}` (real parts, the
values on Hermitian `ρ`). -/
noncomputable def maxCutF {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  max (γ - (cHat C * ρ).trace.re) (∑ j, |(ρ j j).re - (n : ℝ)⁻¹|)

/-- Nannicini pp.200–201, §8.4.2: the inexact subgradient computed from the estimates `estC` of
`Tr(Ĉρ)` and `estD j` of `ρ_jj`: with `u = γ − estC` and `v = Σ_j |estD_j − 1/n|`, return `0` if
`max{u, v} ≤ 3ε/4`; otherwise `−Ĉ` if `u` attains the maximum (`v ≤ u`); otherwise
`Σ_j (I(estD_j > 1/n) − I(1/n > estD_j)) E_jj`. -/
noncomputable def maxCutSubgrad {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (γ ε : ℝ) (estC : ℝ)
    (estD : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  if max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹ then 0
  else if ∑ j, |estD j - (n : ℝ)⁻¹| ≤ γ - estC then -cHat C
  else Matrix.diagonal fun j =>
    if (n : ℝ)⁻¹ < estD j then 1 else if estD j < (n : ℝ)⁻¹ then -1 else 0

end SDP

/-! ### Sanity tests -/

example {ι : Type*} [Fintype ι] [DecidableEq ι] :
    gibbsState (0 : Matrix ι ι ℂ) = ((Fintype.card ι : ℂ))⁻¹ • 1 := by
  simp [gibbsState, NormedSpace.exp_zero, Matrix.trace_one]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (η : ℝ) (G : ℕ → Matrix ι ι ℂ) :
    mmwuIterate η G 1 = gibbsState 0 := by
  simp [mmwuIterate]

example {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (R η w : ℝ) (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) :
    SDP.mmwuRun A C R η w O 0 = Sum.inr [] := rfl

example {m : ℕ} (b : Fin m → ℝ) (γ r c : ℝ) (hc : 0 < c) :
    SDP.genPicPolytope b γ r 0 c = ∅ := by
  ext y; simp [SDP.genPicPolytope]; intros; linarith

example {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (γ ε estC : ℝ) (estD : Fin n → ℝ)
    (h : max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹) :
    SDP.maxCutSubgrad C γ ε estC estD = 0 := by
  simp [SDP.maxCutSubgrad, h]

end QAlgorithms
