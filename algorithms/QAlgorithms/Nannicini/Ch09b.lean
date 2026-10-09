import QAlgorithms.Defs.Adiabatic

/-!
# Nannicini, Chapter 9 (part b): the adiabatic theorem's variants and the QAOA

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Corollary 9.21 (p.223), Theorem 9.23 (p.225), Corollary 9.24 (p.225),
Proposition 9.28 (p.230).

Standing assumptions (§9.1.2, pp.210–213), encoded exactly as for Theorem 9.11 in
`QAlgorithms.Nannicini.Ch09a`. A time-dependent Hamiltonian `H(s)`, `s ∈ [0, 1]`, is Hermitian for
every `s` with twice differentiable entries (Rem. 9.7); `H′`, `H″` are functions `H' H''` with
entrywise `HasDerivWithinAt` on `[0, 1]`. Def. 9.6's max norms `‖H′‖, ‖H″‖` (operator norm, the
frozen `specNorm`) are replaced by arbitrary bounds `N1, N2`; Def. 9.9's gap `γ = min_s γ(s)` by
any `γ > 0` with `HasGapAround (H s) (λ s) γ` for all `s` (every bound is monotone in these
quantities, so the statements are equivalent; no junk supremum enters). The tracked eigenvalue
`λ(s)` is continuous, `φ(s)` is a unit eigenvector for it, and the evolution is Eq. (9.8),
`dψ/ds = iT H(s) ψ`, the frozen `SolvesAdiabaticPlus` (sign `+i`, trap Q12).
-/

universe u

namespace QAlgorithms.Nannicini

/-- Nannicini p.223, Corollary 9.21. The lower bound for `T` stated in Thm. 9.11 suffices to ensure
adiabatic evolution, i.e., a final state such that `‖e^{iθ}|ψ(1)⟩ − |φ(1)⟩‖ ≤ δ` for some `θ`.

The corollary is the conclusion of Theorem 9.11 under Theorem 9.11's hypotheses (pp.212–213), the
source restating it to record that it follows from Theorem 9.17 via `Ĥ(s) = H(s) − λ(s)I`. The
binders are those of `adiabatic_theorem` (Ch09a): `‖H′‖, ‖H″‖, γ` are the bounds `N1, N2, γ`;
Hermiticity of `H(s)` is part of `HasGapAround`. -/
theorem adiabatic_theorem_from_special_case {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (lam : ℝ → ℝ) (hlam : ContinuousOn lam (Set.Icc 0 1)) (φ : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = (lam s : ℂ) • φ s)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) (lam s) γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : 10 ^ 4 / δ ^ 2 * (N1 ^ 3 / γ ^ 4 + N1 * N2 / γ ^ 3) ≤ T)
    (ψ : ℝ → EuclideanSpace ℂ ι) (hψ : SolvesAdiabaticPlus H T ψ) (hψ0 : ψ 0 = φ 0) :
    ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry

/-- Nannicini p.225, Theorem 9.23 (Adiabatic theorem with tighter spectral bound; Thm. 28.1 in
[Childs, 2017]). There exists some constant `c` such that the statement of Thm. 9.11 holds if we
choose `T` satisfying
`T ≥ (c/δ)(‖H′(0)‖/γ(0)² + ‖H′(1)‖/γ(1)² + ∫₀¹ (‖H′(s)‖²/γ(s)³ + ‖H″(s)‖/γ(s)²) ds)`.

The constant `c` is quantified before everything it is uniform over (the space, the Hamiltonian,
`δ`; trap 8). The hypotheses are those of Theorem 9.11 other than the bound on `T`. The
instantaneous gap `γ(s)` (Def. 9.8) enters through any function `g` with
`HasGapAround (H s) (λ s) (g s)` (so `g(s) ≤ γ(s)`), bounded below by some `γ0 > 0` (Thm. 9.11's
gap `γ > 0`); the bound on `T` is decreasing in each `g(s)`, so this is equivalent to using `γ(s)`
itself. `‖H′(s)‖, ‖H″(s)‖` are the pointwise operator norms. The integrand is required to be
integrable on `[0, 1]`: when it is not, the source's integral is `+∞` and no `T` qualifies, while
Lean's integral would be the junk value `0` (trap 2). -/
theorem adiabatic_theorem_integral_gap :
    ∃ c : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (H H' H'' : ℝ → Matrix ι ι ℂ),
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
        HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
        HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s) →
      ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
      ∀ (φ : ℝ → EuclideanSpace ℂ ι),
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = (lam s : ℂ) • φ s) →
      ∀ (g : ℝ → ℝ) (γ0 : ℝ), 0 < γ0 →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, γ0 ≤ g s ∧ HasGapAround (H s) (lam s) (g s)) →
      IntervalIntegrable
        (fun s => specNorm (H' s) ^ 2 / g s ^ 3 + specNorm (H'' s) / g s ^ 2)
        MeasureTheory.volume 0 1 →
      ∀ (δ : ℝ), 0 < δ → ∀ (T : ℝ),
      c / δ * (specNorm (H' 0) / g 0 ^ 2 + specNorm (H' 1) / g 1 ^ 2 +
        ∫ s in (0 : ℝ)..1, (specNorm (H' s) ^ 2 / g s ^ 3 + specNorm (H'' s) / g s ^ 2)) ≤ T →
      ∀ (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus H T ψ → ψ 0 = φ 0 →
      ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry

/-- Nannicini p.225, Corollary 9.24 (Adiabatic theorem for linear interpolation). There exists
some constant `c` such that, when the Hamiltonian `H(s)` performs linear interpolation between an
initial and a final Hamiltonian, as in Eq. (9.6), the statement of Thm. 9.11 holds if we choose `T`
satisfying `T ≥ (c/δ)(‖H_F − H_I‖/γ² + ‖H_F − H_I‖²/γ³)`.

`H(s) = (1 − s)H_I + sH_F` is the frozen `linInterp HI HF s` (Eq. (9.6)), with `H_I, H_F`
Hermitian; it is smooth, `H′ = H_F − H_I`, `H″ = 0`, so no derivative data are supplied. The
constant `c` precedes everything it is uniform over (trap 8). The gap `γ` of Def. 9.9 enters as
any `γ > 0` with `HasGapAround (H s) (λ s) γ` for all `s`, equivalent by monotonicity; the norm is
the operator norm `specNorm`. The other hypotheses are Theorem 9.11's. -/
theorem adiabatic_theorem_linInterp :
    ∃ c : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (HI HF : Matrix ι ι ℂ),
      HI.IsHermitian → HF.IsHermitian →
      ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
      ∀ (φ : ℝ → EuclideanSpace ℂ ι),
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsState (φ s) ∧ act (linInterp HI HF s) (φ s) = (lam s : ℂ) • φ s) →
      ∀ (γ : ℝ), 0 < γ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
      ∀ (δ : ℝ), 0 < δ → ∀ (T : ℝ),
      c / δ * (specNorm (HF - HI) / γ ^ 2 + specNorm (HF - HI) ^ 2 / γ ^ 3) ≤ T →
      ∀ (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus (linInterp HI HF) T ψ → ψ 0 = φ 0 →
      ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry

/-- Nannicini p.230, Proposition 9.28. Consider the time-dependent Hamiltonian
`H(s) = (1 − s)H_I + sH_F` (9.41), where `H_F = Σ_x f(x)|x⟩⟨x|` (9.39) and `H_I = Σ_j σ_j^X`
(9.40). For `p ∈ ℕ`, `p > 0`, let `β, θ ∈ [0, 2π]^p`, and define
`U_QAOA(p, β, θ) := e^{−iβ_p H_I} e^{−iθ_p H_F} ⋯ e^{−iβ_1 H_I} e^{−iθ_1 H_F}` (9.42). Then, for any
`δ > 0` and for `p → ∞`, there exists a choice `β*, θ*` of `β, θ` such that `U_QAOA(p, β*, θ*)`
approximates an adiabatic evolution of `H(s)`, and in particular
`lim_{p→∞} ‖U_QAOA(p, β*, θ*)(H|0⟩)^{⊗n} − |φ(1)⟩‖ ≤ δ`, where `|φ(1)⟩` is an eigenstate of
`H(1) = H_F` with maximum eigenvalue, encoding a solution to problem (9.38).

`f : {0,1}^n → ℝ` is arbitrary (problem (9.38)); `H_F` is the frozen `problemHamiltonian f`,
`H_I` the frozen `qaoaMixer n`, `U_QAOA` the frozen `qaoaUnitary f p β θ` (index `k : Fin p` is the
source's `k + 1`; the first factor applied is `e^{−iθ_1 H_F}`). The maximum eigenvalue of `H_F` is
`max_x f(x)`. The limit claim, with angles depending on `p`, is stated as: for every `δ > 0` there
are a unit eigenvector `φ` of `H_F` with eigenvalue `max f` and a `P ≥ 1` such that for every
`p ≥ P` some angles in `[0, 2π]^p` bring the QAOA state within `δ` of `φ`. The global phase of
Thm. 9.11 is absorbed into `φ` (a phase multiple of a top eigenvector is one). The informal
"approximates an adiabatic evolution" is the "in particular" claim, which is what is stated. -/
theorem qaoa_approximates_adiabatic {n : ℕ} (f : Qubits n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : EuclideanSpace ℂ (Qubits n), IsState φ ∧
      act (problemHamiltonian f) φ = ((Finset.univ.sup' Finset.univ_nonempty f : ℝ) : ℂ) • φ ∧
      ∃ P : ℕ, 1 ≤ P ∧ ∀ p : ℕ, P ≤ p →
        ∃ β θ : Fin p → ℝ, (∀ k, β k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          (∀ k, θ k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          ‖act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n)) - φ‖ ≤ δ := by
  sorry

end QAlgorithms.Nannicini
