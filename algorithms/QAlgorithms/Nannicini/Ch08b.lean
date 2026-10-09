import QAlgorithms.Defs.SDP

/-!
# Nannicini, Chapter 8 (part b): the MaxCut SDP relaxation by inexact mirror descent

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §8.4.2–8.4.3: Proposition 8.28 (p.201), Lemma 8.29 (p.201), Theorem 8.30 (p.202),
Lemma 8.33 (p.204). Proposition 8.34 (p.204) is not stated (see `HARD.md`).

Standing assumptions (§8.4, pp.198–200). `C ∈ ℝ^{n×n}` is symmetric (p.198), given here as a real
matrix `C` with `C.IsSymm` and used through its complex image `C.map (↑)`; `Ĉ = C/‖C‖_F` is the
frozen `SDP.cHat` and needs `C ≠ 0`. The binary-search guess is `γ ∈ [−1, 1]` (p.199) and the
precision is `ϵ > 0`. The function `f_γ(ρ) = max{γ − Tr(Ĉρ), Σ_j |ρ_jj − 1/n|}` of Eq. (8.26) is the
frozen `SDP.maxCutF`. The estimate-driven subgradient of pp.200–201 is the frozen
`SDP.maxCutSubgrad`, fed with estimates `estC` of `Tr(Ĉρ)` and `estD j` of `ρ_jj` satisfying
Eq. (8.27). Subgradients and `ϵ`-subgradients (Def. 5.24, p.120) are the frozen `IsEpsSubgradOn`;
the vector space is the real space of Hermitian matrices (Rem. 8.6, 8.9: subgradient steps are taken
in the space of Hermitian matrices), and the dual pairing is the trace inner product
`⟨G, X⟩ = Tr(G X†)` (frozen `traceRePairing`). The iterates of Alg. 6 (p.183) are the frozen
`mmwuIterate`: `ρ^(t) = exp(−η Σ_{τ<t} G^(τ)) / Tr(⋯)`, `ρ^(1) = I/n`. `log` is base 2 (p.11).
-/

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

/-- Nannicini p.201, Proposition 8.28, **corrected** (trap 30). As printed: "Let `G^(t)` be
computed according to the algorithm above. Then `G^(t) ∈ ∂_{ϵ/2} f_γ(ρ^(t))`."

The zero branch is false as printed: the book's proof only shows that `0` is an `ϵ`-subgradient
(not an `ϵ/2`-subgradient) there. Counterexample: `n = 2`, `γ = −1`,
`ρ = diag(1/2 + ϵ/2, 1/2 − ϵ/2)`, diagonal estimates `1/2 ± 3ϵ/8` and the exact value of
`Tr(Ĉρ)`; the estimated maximum is `3ϵ/4`, so `G = 0`, while `f_γ(ρ) = ϵ` and `f_γ(I/2) = 0`.
The book itself says (p.201) that the zero branch only signals `f_γ(ρ^(t)) ≤ ϵ`. Stated:

1. if the estimated maximum is at most `3ϵ/4`, then `G = 0` and `f_γ(ρ) ≤ ϵ`;
2. otherwise `G ∈ ∂_{ϵ/2} f_γ(ρ)`, the `ϵ/2`-subgradient inequality holding at every Hermitian
   matrix.

The current iterate `ρ^(t)` is any density matrix `ρ`; the estimates satisfy Eq. (8.27). -/
theorem maxCutSubgrad_mem_epsSubdiff {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDensityMatrix ρ) (estC : ℝ) (estD : Fin n → ℝ)
    (hestC : |estC - (cHat (C.map ((↑) : ℝ → ℂ)) * ρ).trace.re| ≤ ε * 4⁻¹)
    (hestD : ∑ j, |estD j - (ρ j j).re| ≤ ε * 4⁻¹) :
    (max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹ →
        maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD = 0 ∧
          maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρ ≤ ε) ∧
      (3 * ε * 4⁻¹ < max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) →
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) ρ
          (traceRePairing (maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD))) := by
  sorry

/-- Nannicini p.201, Lemma 8.29. Let `h_1, …, h_m` be 1-Lipschitz convex functions and
`f(x) = max_i h_i(x)`. For points `x̄, x̂` with `‖x̄ − x̂‖ ≤ ϵ/4`, let `j ∈ argmax_i h_i(x̂)`. Then,
for `g ∈ ∂h_j(x̂)`, we have `g ∈ ∂_{ϵ̂} f(x̄)`, where `ϵ̂ = (ϵ/4)(‖g‖_* + 1)`.

The space is any real normed space `E` (in Prop. 8.28 it is the space of Hermitian matrices with
the trace norm). Subgradients are elements of the dual `E*` (Def. 5.24), here continuous linear
functionals, and the dual norm `‖g‖_* = max_{‖x‖=1} ⟨g, x⟩` (Def. 8.4, p.181) is the operator norm
of `g`. The index `j` is in the argmax: `h_i(x̂) ≤ h_j(x̂)` for all `i`; the maximum over the
(nonempty, since `j` exists) index set is `Finset.sup'`. -/
theorem epsSubgrad_of_subgrad_active_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (h : Fin m → E → ℝ) (hLip : ∀ i, LipschitzWith 1 (h i))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (h i)) (ε : ℝ) (xbar xhat : E)
    (hdist : ‖xbar - xhat‖ ≤ ε * 4⁻¹) (j : Fin m) (hj : ∀ i, h i xhat ≤ h j xhat)
    (g : E →L[ℝ] ℝ) (hg : IsEpsSubgradOn Set.univ (h j) 0 xhat g.toLinearMap) :
    IsEpsSubgradOn Set.univ
      (fun x => Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ fun i => h i x)
      (ε * 4⁻¹ * (‖g‖ + 1)) xbar g.toLinearMap := by
  sorry

/-- Nannicini p.202, Theorem 8.30 (Convergence of mirror descent for MaxCut SDP). Suppose there
exists `ρ* ∈ S^n_{+,1}` such that `f_γ(ρ*) = 0`. Then the mirror descent algorithm Alg. 6 with step
size `η = ϵ/16`, inexact subgradients `G^(t) ∈ ∂_{ϵ/2} f_γ(ρ^(t))`, and number of steps
`T = (64/ϵ²) log n`, returns density matrices `ρ^(1), …, ρ^(T)` such that
`f_γ((1/T) Σ_{t=1}^T ρ^(t)) ≤ ϵ`.

Alg. 6 obtains `G^(t)` for `t = 1, …, T − 1` and returns `ρ^(1), …, ρ^(T)`, `ρ^(t)` being
`mmwuIterate η G t`; each `G^(t)` is a Hermitian matrix (an element of the dual of the space of
Hermitian matrices) and an `ϵ/2`-subgradient of `f_γ` at `ρ^(t)` over all Hermitian matrices.
Two recorded adjustments: `T = ⌈(64/ϵ²) log₂ n⌉` (the printed `T` need not be an integer; the
ceiling only enlarges it), and `n ≥ 2` (at `n = 1`, `log n = 0` gives `T = 0` and the average of
no iterates is `0`, with `f_γ(0) = max(γ, 1) > ϵ` for `ϵ < 1`). -/
theorem mirrorDescent_maxCut_converges {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (hfeas : ∃ ρs : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix ρs ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρs = 0)
    (G : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hG : ∀ t, 1 ≤ t → t < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      (G t).IsHermitian ∧
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) (mmwuIterate (ε * 16⁻¹) G t)
          (traceRePairing (G t))) :
    (∀ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊,
        IsDensityMatrix (mmwuIterate (ε * 16⁻¹) G t)) ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ
        (((⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ : ℕ) : ℂ)⁻¹ •
          ∑ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊, mmwuIterate (ε * 16⁻¹) G t) ≤ ε := by
  sorry

/-- Nannicini p.204, Lemma 8.33. For every iteration `t` of Alg. 6 applied to (MaxCutSDP-F) as
described in Sect. 8.4.2, `H^(t) = y_1 Ĉ + y_2 D` for some vector `y ∈ ℝ²`, where `D` is a
diagonal matrix. Furthermore, `‖y‖_1 ≤ (4/ϵ) log n`.

The run of §8.4.2: `η = ϵ/16`, `T = ⌈(64/ϵ²) log₂ n⌉` (ceiling as in Theorem 8.30), and for
`τ = 1, …, T − 1` the subgradient `G^(τ)` is the estimate-driven matrix `maxCutSubgrad`
computed from estimates `estC τ`, `estD τ` of `Tr(Ĉρ^(τ))`, `ρ^(τ)_jj` satisfying Eq. (8.27), with
`ρ^(τ) = mmwuIterate η G τ`. The Hamiltonian is `H^(t) = −η Σ_{τ<t} G^(τ)` (Prop. 8.7, Alg. 6), for
`t = 1, …, T`. The normalization `|D_jj| ≤ 1` (proof, p.204: "we can keep `D` normalized so that its
entries are less than 1 in absolute value") is part of the conclusion: without it the bound on
`‖y‖_1` says nothing. -/
theorem maxCut_hamiltonian_structure {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (estC : ℕ → ℝ) (estD : ℕ → Fin n → ℝ)
    (hest : ∀ τ, 1 ≤ τ → τ < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      |estC τ - (cHat (C.map ((↑) : ℝ → ℂ)) *
          mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ).trace.re|
          ≤ ε * 4⁻¹ ∧
        ∑ j, |estD τ j - (mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ j j).re|
          ≤ ε * 4⁻¹)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊) :
    ∃ (y : Fin 2 → ℝ) (d : Fin n → ℂ), (∀ j, ‖d j‖ ≤ 1) ∧
      -((ε * 16⁻¹ : ℝ) : ℂ) • ∑ τ ∈ Finset.Ico 1 t,
          maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC τ) (estD τ) =
        ((y 0 : ℝ) : ℂ) • cHat (C.map ((↑) : ℝ → ℂ)) + ((y 1 : ℝ) : ℂ) • Matrix.diagonal d ∧
      |y 0| + |y 1| ≤ 4 * ε⁻¹ * Real.logb 2 n := by
  sorry

end QAlgorithms.Nannicini
