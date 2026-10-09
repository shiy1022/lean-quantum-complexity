import QAlgorithms.Defs.Adiabatic

/-!
# Nannicini, Chapter 9 (part a): the Ising Hamiltonian and the adiabatic theorem

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §9.1: Proposition 9.4 (pp.209–210), Theorem 9.11 (pp.212–213), Theorem 9.17 (p.218),
Lemma 9.18 (p.218). Lemma 9.20 (p.221) is not stated (see `HARD.md`).

Standing assumptions (§9.1.2, pp.210–212). A time-dependent Hamiltonian `H(s)`, `s ∈ [0, 1]`, is
Hermitian for every `s` (Def. 6.1) with twice differentiable entries (p.210, Rem. 9.7); `H′`, `H″`
are the entrywise derivatives, here functions `H' H''` with entrywise `HasDerivWithinAt` on
`[0, 1]` (one-sided at the endpoints). Def. 9.6: `‖H′‖ := max_s ‖H′(s)‖` (operator norm, the
frozen `specNorm`), likewise `‖H″‖`; these maxima are replaced by arbitrary bounds `N1, N2` with
`‖H′(s)‖ ≤ N1`, `‖H″(s)‖ ≤ N2` for all `s` — every statement is monotone in these bounds, so the
version for all such bounds is equivalent to the version at the maxima, and no junk value of a
real supremum enters (traps 5, 20). Defs. 9.8–9.9: the spectral gap `γ = min_s γ(s)` around the
tracked eigenvalue `λ(s)` is replaced, by the same monotonicity, by any `γ > 0` with
`HasGapAround (H s) (λ s) γ` for all `s` (`λ(s)` simple, every other eigenvalue at distance
`≥ γ`). The eigenvalue branch `λ` is continuous (p.211). The adiabatic evolution is
Eq. (9.8), `dψ/ds = iT H(s) ψ`, the frozen `SolvesAdiabaticPlus` (sign `+i`, trap Q12).
-/

namespace QAlgorithms.Nannicini

open QAlgorithms.Stabilizer

/-- Nannicini pp.209–210, Proposition 9.4. The Hamiltonian
`H := Σ_{j,k=1}^n A_jk σ_j^Z σ_k^Z + Σ_{j=1}^n c_j σ_j^Z` satisfies the properties:
`⟨x|H|x⟩ = zᵀAz + cᵀz ∀x ∈ {0,1}^n`, `⟨j|H|k⟩ = 0 ∀j ≠ k`, where `z = 1 − 2x ∈ {−1,+1}^n`.

`A ∈ ℝ^{n×n}` and `c ∈ ℝ^n` are the data of problem (9.3), arbitrary (the proof does not use
`A = Q/4`, `c = −Qᵀ1/2`). `σ_j^Z` (Eq. (9.4)) is the Pauli `Z` on wire `j` (the source's qubit
`j + 1`), identity elsewhere; `⟨y|H|w⟩` is the matrix entry `H y w`; `x_j` is read as `0/1` by
`boolPoint`. -/
theorem isingHamiltonian_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    let σ : Fin n → Matrix (Qubits n) (Qubits n) ℂ := fun j => CliffordOp.mat (CliffordOp.pauli j Pauli.Z)
    let H : Matrix (Qubits n) (Qubits n) ℂ :=
      ∑ j : Fin n, ∑ k : Fin n, ((A j k : ℝ) : ℂ) • (σ j * σ k) + ∑ j : Fin n, ((c j : ℝ) : ℂ) • σ j
    (∀ x : Qubits n,
      H x x = (((∑ j : Fin n, ∑ k : Fin n, A j k * (1 - 2 * boolPoint x j) * (1 - 2 * boolPoint x k)) +
        ∑ j : Fin n, c j * (1 - 2 * boolPoint x j) : ℝ) : ℂ)) ∧
      ∀ y w : Qubits n, y ≠ w → H y w = 0 := by
  sorry

/-- Nannicini pp.212–213, Theorem 9.11 (Adiabatic theorem). Let `H(s)` be a time-dependent
Hamiltonian, let `λ(s)` be an eigenvalue of `H(s)`, and let `|φ(s)⟩` be an eigenstate of `H(s)`
with eigenvalue `λ(s)`. Assume that there is a spectral gap `γ > 0` around `λ(s)`. Assume further
that, from the initial state `|φ(0)⟩`, we apply the time evolution `d|ψ(s)⟩/ds = iT H(s)|ψ(s)⟩`,
`s ∈ [0, 1]`, `|ψ(0)⟩ = |φ(0)⟩`, and for some `δ > 0`, `T` satisfies
`T ≥ (10⁴/δ²)(‖H′‖³/γ⁴ + ‖H′‖‖H″‖/γ³)`. Then the system approximately remains in the
instantaneous eigenstate `|φ(s)⟩` with eigenvalue `λ(s)` for all `s`, and in particular, the final
state `|ψ(1)⟩` has Euclidean distance at most `δ` from `|φ(1)⟩`, up to global phase:
`‖e^{iθ}|ψ(1)⟩ − |φ(1)⟩‖ ≤ δ` for some `θ`.

Stated is the precise claim, the "in particular" about `ψ(1)`; the unquantified "approximately
remains … for all s" carries no stated error. Hermiticity of `H(s)` is part of `HasGapAround`.
`‖H′‖, ‖H″‖, γ` are the bounds `N1, N2, γ` of the module docstring. -/
theorem adiabatic_theorem {ι : Type*} [Fintype ι] [DecidableEq ι] (H H' H'' : ℝ → Matrix ι ι ℂ)
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

/-- Nannicini p.218, Theorem 9.17 (Special case of the adiabatic theorem). Let `H(s)` be a
time-dependent Hamiltonian, and let `|φ(s)⟩` be an eigenstate of `H(s)` with eigenvalue
`λ(s) = 0` for all `s ∈ [0, 1]`. Assume that there is a spectral gap `γ > 0` around `λ(s) = 0`,
i.e., all other eigenvalues are at least `γ` in absolute value. Assume further that, from the
initial state `|φ(0)⟩`, we apply the time evolution `d|ψ(s)⟩/ds = iT H(s)|ψ(s)⟩`, `s ∈ [0, 1]`,
`|ψ(0)⟩ = |φ(0)⟩`, and for some `δ > 0`, `T` satisfies
`T ≥ (10³/δ²) max{‖H′‖³/γ⁴, ‖H′‖‖H″‖/γ³}`. Then the system approximately remains in the
instantaneous eigenstate `|φ(s)⟩` with eigenvalue `0` for all `s`, and in particular, the final
state `|ψ(1)⟩` has Euclidean distance at most `δ` from `|φ(1)⟩`, up to global phase:
`‖e^{iθ}|ψ(1)⟩ − |φ(1)⟩‖ ≤ δ` for some `θ`.

The constant `10³` is the printed one (also Eq. (9.25)). Conventions as in `adiabatic_theorem`;
the gap is `HasGapAround (H s) 0 γ` (`0` a simple eigenvalue, all others `≥ γ` in absolute value). -/
theorem adiabatic_theorem_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (φ : ℝ → EuclideanSpace ℂ ι) (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : 10 ^ 3 / δ ^ 2 * max (N1 ^ 3 / γ ^ 4) (N1 * N2 / γ ^ 3) ≤ T)
    (ψ : ℝ → EuclideanSpace ℂ ι) (hψ : SolvesAdiabaticPlus H T ψ) (hψ0 : ψ 0 = φ 0) :
    ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry

/-- Nannicini p.218, Lemma 9.18 (Lem. 3.2 in [Ambainis and Regev, 2004]). In the context of
Thm. 9.17, assume the phase of `|φ(s)⟩` is chosen so that `⟨φ′(s)|φ(s)⟩ = 0`. Then
`‖|φ′⟩‖ ≤ ‖H′‖/γ` and `‖|φ″⟩‖ ≤ ‖H″‖/γ + 3‖H′‖²/γ²`.

The context of Thm. 9.17 that the lemma uses is the Hamiltonian and its zero eigenvector with gap
`γ`; the evolution `ψ`, `T`, `δ` play no role and are omitted. `φ′, φ″` are the entrywise
derivatives (Rem. 9.19), functions `φ' φ''` with `HasDerivWithinAt` on `[0, 1]` (twice
differentiability of `φ` is implicit, since `φ′, φ″` appear). The max norms `‖|φ′⟩‖, ‖|φ″⟩‖`
(Def. 9.6) are bounded pointwise for every `s`, which is equivalent. -/
theorem adiabatic_eigvec_deriv_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (φ φ' φ'' : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (hφ' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s)
    (hφ'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ' (φ'' s) (Set.Icc 0 1) s)
    (hphase : ∀ s ∈ Set.Icc (0 : ℝ) 1, inner ℂ (φ' s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖φ' s‖ ≤ N1 / γ ∧ ‖φ'' s‖ ≤ N2 / γ + 3 * N1 ^ 2 / γ ^ 2 := by
  sorry

end QAlgorithms.Nannicini
