import QAlgorithms.Defs.Adiabatic

/-!
# Nannicini, Chapter 8 (first part): mirror descent, MMWU, the MMWU SDP solver

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §8.1.2–§8.3.1. Matrices are `n × n` complex matrices indexed by `Fin n`; the
source's 1-based indices `j = 1, …, m` are `Fin m` (0-based), so the source's `A^(1)`, `b_1`,
`e_1` sit at index `0`. Traces of products of Hermitian matrices are real and are written with
`.re`. Iteration indices `t` are the source's, 1-based. The frozen objects used are
`gibbsState`, `mmwuIterate`, `qRelEntropy`, `IsEntropicMirrorDescent` and the namespace
`QAlgorithms.SDP` (`PrimalFeasible`, `DualFeasible`, `IsDualOptimal`, `picPolytope`,
`IsPICOracle`, `mmwuSDP`, `genPicPolytope`).
-/

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder

/-- Nannicini pp.182–183, Proposition 8.7. Let `G^(1), G^(2), …` be Hermitian `n × n` matrices
(`n ≥ 1`), `η ∈ ℝ`, and let `H^(1) = 0`, `H^(t+1) = H^(t) − η G^(t)`. Then the Gibbs states
`ρ^(t) = exp(H^(t)) / Tr exp(H^(t))` coincide with the iterates of mirror descent with the von
Neumann negative entropy as mirror map and initial point `I/n` (Eq. (8.8): `ρ^(t+1)` minimizes the
quantum relative entropy `D(·‖exp(log ρ^(t) − ηG^(t)))` over the density matrices). Both
directions: the Gibbs sequence satisfies this recursion, and every sequence satisfying it equals
the Gibbs sequence at every `t ≥ 1`. -/
theorem gibbs_eq_mirrorDescent {n : ℕ} (hn : 0 < n) (η : ℝ)
    (G : ℕ → Matrix (Fin n) (Fin n) ℂ) (hG : ∀ t, (G t).IsHermitian)
    (H : ℕ → Matrix (Fin n) (Fin n) ℂ) (hH1 : H 1 = 0)
    (hHsucc : ∀ t ≥ 1, H (t + 1) = H t - (η : ℂ) • G t) :
    IsEntropicMirrorDescent η G (fun t => gibbsState (H t)) ∧
      ∀ ρ : ℕ → Matrix (Fin n) (Fin n) ℂ, IsEntropicMirrorDescent η G ρ →
        ∀ t ≥ 1, ρ t = gibbsState (H t) := by
  sorry

/-- Nannicini p.185, Theorem 8.10 (Thm. 3.1 in [Arora and Kale, 2016]). Let `n ≥ 1`,
`0 < η ≤ 1` (Alg. 6's input condition), and let `M^(1), …, M^(T)` be Hermitian `n × n` loss
matrices with operator norm `‖M^(t)‖ ≤ 1`. Running Alg. 6 with subgradients `G^(t) = M^(t)`, i.e.
`ρ^(t) = exp(−η Σ_{τ<t} M^(τ)) / Tr exp(−η Σ_{τ<t} M^(τ))`, produces density matrices
`ρ^(1), …, ρ^(T)` with
`Tr(Σ_t M^(t) ρ^(t)) ≤ λ_min(Σ_t M^(t)) + η Tr(Σ_t (M^(t))² ρ^(t)) + ln n / η` (8.11). -/
theorem mmwu_regret {n : ℕ} (hn : 0 < n) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (T : ℕ)
    (M : ℕ → Matrix (Fin n) (Fin n) ℂ) (hMherm : ∀ t ∈ Finset.Icc 1 T, (M t).IsHermitian)
    (hMnorm : ∀ t ∈ Finset.Icc 1 T, specNorm (M t) ≤ 1) :
    (∀ t ∈ Finset.Icc 1 T, IsDensityMatrix (mmwuIterate η M t)) ∧
      (∑ t ∈ Finset.Icc 1 T, M t * mmwuIterate η M t).trace.re ≤
        minEigenvalue (∑ t ∈ Finset.Icc 1 T, M t) +
          η * (∑ t ∈ Finset.Icc 1 T, M t ^ 2 * mmwuIterate η M t).trace.re +
          Real.log n / η := by
  sorry

/-- Nannicini p.188, Lemma 8.12 (Lem. 4.2 in [Arora and Kale, 2016]). Standing assumptions of
§8.2.2 (p.187): `C, A^(j)` Hermitian, (a) `A^(1) = I` and `b_1 = R > 0`, (b) `‖C‖ ≤ 1`. Let
`ϵ > 0`, `γ ∈ ℝ` and `X ⪰ 0`.
1. If `P_ϵ(X)` (Eq. (8.16)) is empty then, up to rescaling, `X` is feasible for (P-SDP) with
   objective value at least `γ`: some `z ≥ 0` makes `zX` primal feasible with `Tr(C zX) ≥ γ`.
2. If `P_ϵ(X)` is nonempty then `X` is not feasible for (P-SDP), or `Tr(CX) ≤ γ + ϵ`. -/
theorem picPolytope_certificate {n m : ℕ} (hm : 0 < m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (hb1 : b ⟨0, hm⟩ = R) (hR : 0 < R) (hC : specNorm C ≤ 1)
    (γ ε : ℝ) (hε : 0 < ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) :
    (picPolytope A b C γ ε X = ∅ →
      ∃ z : ℝ, 0 ≤ z ∧ PrimalFeasible A b ((z : ℂ) • X) ∧
        γ ≤ (C * ((z : ℂ) • X)).trace.re) ∧
    ((picPolytope A b C γ ε X).Nonempty →
      ¬ PrimalFeasible A b X ∨ (C * X).trace.re ≤ γ + ε) := by
  sorry

/-- Nannicini pp.189–191, Theorem 8.15 (Thm. 4.4 in [Arora and Kale, 2016], Thm. 5 in
[van Apeldoorn, 2020]). Under assumptions (a) `A^(1) = I`, `b_1 = R > 0` and (b) `‖C‖ ≤ 1`, with
`ϵ > 0`, width bound `w > 0` and any `PIC-Oracle_{ϵ/3}` of width at most `w` (Defs. 8.11, 8.13),
Alg. 7 (`mmwuSDP`, with `T = ⌈9w²R² ln n/ϵ²⌉`, `η = √(ln n/T)`) returns either a matrix `X`
which, rescaled as in Lemma 8.12, is feasible for (P-SDP) with objective value at least `γ`, or a
vector `ȳ` feasible for (D-SDP) with `bᵀȳ ≤ γ + ϵ`.

Added hypothesis `n ≥ 2`: at `n = 1`, `ln n = 0`, so `T = 0` and `η = √(0/0)`; the loop never
runs and the returned `(ϵ/R) e_1` need not be dual feasible (`C = [1]`, `R = 1`, `ϵ = 1/2`,
`γ = 2`). The source's proof divides by `T` and by `ln n`. -/
theorem mmwuSDP_correct {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ) (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (hb1 : b ⟨0, hm⟩ = R) (hR : 0 < R) (hC : specNorm C ≤ 1)
    (γ ε w : ℝ) (hε : 0 < ε) (hw : 0 < w)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ))
    (hO : IsPICOracle A b C γ (ε / 3) w O) :
    (∀ X : Matrix (Fin n) (Fin n) ℂ, mmwuSDP A C R ε w O = Sum.inl X →
      ∃ z : ℝ, 0 ≤ z ∧ PrimalFeasible A b ((z : ℂ) • X) ∧
        γ ≤ (C * ((z : ℂ) • X)).trace.re) ∧
    (∀ y : Fin m → ℝ, mmwuSDP A C R ε w O = Sum.inr y →
      DualFeasible A C y ∧ ∑ j, b j * y j ≤ γ + ε) := by
  sorry

/-- Nannicini pp.192–193, Proposition 8.19 ([van Apeldoorn, 2020]). Standing assumptions:
(a) `A^(1) = I`, `b_1 = R > 0`; (b) `‖C‖ ≤ 1`; (c) some optimal solution of (D-SDP) has
`‖y‖₁ ≤ r`, with `r ≥ 1`. Let `X ⪰ 0`, `ρ = X / Tr(X)` with `Tr(X) ≤ R`, `θ ≥ 0`, and let
`ã ∈ ℝ^m`, `c̃ ∈ ℝ` with `|Tr(Cρ) − c̃| ≤ θ` and `|Tr(A^(j)ρ) − ã_j| ≤ θ` for all `j`. Then
`P_0(X) ∩ {‖y‖₁ ≤ r} ⊆ P̂(ã, c̃ − (r + 1)θ) ⊆ P_{4Rrθ}(X) ∩ {‖y‖₁ ≤ r}`.
At `X = 0` Lean's `0⁻¹ = 0` gives `ρ = 0`; the chain still holds there. -/
theorem genPicPolytope_sandwich {n m : ℕ} (hm : 0 < m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ) (R r : ℝ)
    (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (hb1 : b ⟨0, hm⟩ = R) (hR : 0 < R) (hC : specNorm C ≤ 1)
    (hr : 1 ≤ r) (hopt : ∃ y : Fin m → ℝ, IsDualOptimal A C b y ∧ ∑ j, |y j| ≤ r)
    (γ : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) (hXR : X.trace.re ≤ R)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ = (X.trace)⁻¹ • X)
    (θ : ℝ) (hθ : 0 ≤ θ) (atil : Fin m → ℝ) (ctil : ℝ)
    (hc : |(C * ρ).trace.re - ctil| ≤ θ) (ha : ∀ j, |(A j * ρ).trace.re - atil j| ≤ θ) :
    picPolytope A b C γ 0 X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r} ⊆
        genPicPolytope b γ r atil (ctil - (r + 1) * θ) ∧
      genPicPolytope b γ r atil (ctil - (r + 1) * θ) ⊆
        picPolytope A b C γ (4 * R * r * θ) X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r} := by
  sorry

/-- Chunk-local (Nannicini p.195, Prop. 8.21: the register `|ã_j⟩`). The source does not say how a
real number is held in a register; this fixes the word-size model: a `p`-qubit register `z` holds
the offset-binary fixed-point number `(bitsToNat z − 2^{p−1}) / 2^f` (most significant bit first,
`f` fractional bits). -/
noncomputable def fixedPointVal (p f : ℕ) (z : Qubits p) : ℝ :=
  ((bitsToNat z : ℝ) - 2 ^ (p - 1)) / 2 ^ f

/-- Chunk-local (Nannicini p.195, Prop. 8.21: the circuit `U`). `U` is a unitary on an index
register of `⌈log₂ m⌉` qubits, a `p`-qubit value register and a `g`-qubit garbage register with
`U|j⟩|0⟩|0⟩ = |j⟩|ã_j⟩|ψ_j⟩` for every `j ∈ [m]` (`j` written in binary, `natToBits`), where
`ã_j` is a fixed-point number (`fixedPointVal p f`) with `|t_j − ã_j| ≤ θ` and `ψ_j` is a unit
vector. With `θ = 0` it is an exact data oracle. -/
def IsFixedPointValueOracle {m : ℕ} (p f g : ℕ) (t : Fin m → ℝ) (θ : ℝ)
    (U : Matrix (Qubits (Nat.clog 2 m + p + g)) (Qubits (Nat.clog 2 m + p + g)) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Qubits (Nat.clog 2 m + p + g)) ℂ ∧
    ∃ code : Fin m → Qubits p, (∀ j, |t j - fixedPointVal p f (code j)| ≤ θ) ∧
      ∀ j : Fin m, ∃ ψ : EuclideanSpace ℂ (Qubits g), IsState ψ ∧
        act U (ket (Fin.append (Fin.append (natToBits (Nat.clog 2 m) j) (fun _ : Fin p => false))
            (fun _ : Fin g => false))) =
          WithLp.toLp 2 fun z : Qubits (Nat.clog 2 m + p + g) =>
            if (fun i => z (Fin.castAdd g i)) = Fin.append (natToBits (Nat.clog 2 m) j) (code j)
            then ψ (fun l => z (Fin.natAdd (Nat.clog 2 m + p) l)) else 0

open Classical in
/-- Corrected statement. Nannicini p.195, Proposition 8.21 (informal; the source defers the precise
version to Lem. 16 of [van Apeldoorn et al., 2020b], not on disk). Printed: given a circuit `U`
with `U|j⟩|0⟩|0⟩ = |j⟩|ã_j⟩|ψ_j⟩`, `|Tr(A^(j)ρ) − ã_j| ≤ θ`, a quantum algorithm with `Õ(√m)`
calls to `U` and as many gates "with high probability returns a vector in
`P_{4Rrθ}(X) ∩ {‖y‖₁ ≤ r}` if `P_0(X) ∩ {‖y‖₁ ≤ r}` is nonempty, and returns 'failure' if
`P_0(X) ∩ {‖y‖₁ ≤ r}` is empty".

Changes, each forced by a gap of the printed claim:
1. *High probability*: success probability `≥ 1 − δ` for every `δ ∈ (0,1)`, with cost
   polylogarithmic in `1/δ` (the reading of Rem. 8.20, p.194).
2. *`Õ(√m)`*: `K √m (ln(2+m) + ln(2+1/δ) + p + 1)^e` with absolute `K, e` quantified first; the
   suppressed factors are polylogarithmic in `m`, `1/δ` and polynomial in the word size `p`.
3. *Cost model*: the algorithm is an oracle circuit over all two-qubit unitaries
   (`twoQubitGateSet`), started in `|0…0⟩`, measured in the computational basis, the outcome
   mapped classically to a vector or `none` ("failure"); calls to `U` (plain, inverse or
   controlled) are `queryCount 0`. Numbers are `p`-bit fixed point (`fixedPointVal`).
4. *Missing inputs*: the procedure (pp.194–195) needs `c̃` with `|Tr(Cρ) − c̃| ≤ θ` (Prop. 8.19)
   and the points `b_j`; `c̃, γ, r, θ` are given classically, and `b` through an exact oracle `B`
   of the same form (index `1`), whose calls are bounded too (loading `b` into gates would cost
   `Θ(m)` gates, so the gate claim needs this access).
5. *Failure clause*: the algorithm only sees `θ`-accurate traces, so it cannot detect emptiness
   of `P_0(X)`, which is defined by exact traces. Stated instead: failure is returned only when
   `P_0(X) ∩ {‖y‖₁ ≤ r}` is empty (when it is empty, the output is failure or a vector of
   `P_{4Rrθ}(X) ∩ {‖y‖₁ ≤ r}`), which is what the procedure through Prop. 8.19 gives.

The algorithm depends on `m, p, f, g, δ, γ, r, θ, c̃` only, never on `A, b, C, X, n`. Standing
assumptions (a), (b), (c) and the hypotheses of Prop. 8.19 are binders. -/
theorem dualVector_search :
    ∃ (K : ℝ) (e : ℕ), 0 < K ∧
    ∀ (m : ℕ) (hm : 0 < m) (p f g : ℕ) (δ : ℝ), 0 < δ → δ < 1 → ∀ (γ r θ ctil : ℝ),
    ∃ (N : ℕ) (c : OracleCircuit twoQubitGateSet (fun _ : Fin 2 => Nat.clog 2 m + p + g) N)
      (out : Qubits N → Option (Fin m → ℝ)),
      (c.queryCount 0 : ℝ) ≤
        K * Real.sqrt m * (Real.log (2 + m) + Real.log (2 + 1 / δ) + p + 1) ^ e ∧
      (c.queryCount 1 : ℝ) ≤
        K * Real.sqrt m * (Real.log (2 + m) + Real.log (2 + 1 / δ) + p + 1) ^ e ∧
      (c.gateCount : ℝ) ≤
        K * Real.sqrt m * (Real.log (2 + m) + Real.log (2 + 1 / δ) + p + 1) ^ e ∧
      ∀ (n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
        (C : Matrix (Fin n) (Fin n) ℂ) (R : ℝ),
        (∀ j, (A j).IsHermitian) → C.IsHermitian → A ⟨0, hm⟩ = 1 → b ⟨0, hm⟩ = R → 0 < R →
        specNorm C ≤ 1 → 1 ≤ r → (∃ y : Fin m → ℝ, IsDualOptimal A C b y ∧ ∑ j, |y j| ≤ r) →
        ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef → X.trace.re ≤ R → 0 ≤ θ →
        |(C * ((X.trace)⁻¹ • X)).trace.re - ctil| ≤ θ →
        ∀ U B : Matrix (Qubits (Nat.clog 2 m + p + g)) (Qubits (Nat.clog 2 m + p + g)) ℂ,
        IsFixedPointValueOracle p f g (fun j => (A j * ((X.trace)⁻¹ • X)).trace.re) θ U →
        IsFixedPointValueOracle p f g b 0 B →
        probEvent (act (c.unitary fun k => if k = 0 then U else B) (zeroKet N))
          (fun z => (∃ y, out z = some y ∧
              y ∈ picPolytope A b C γ (4 * R * r * θ) X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r}) ∨
            (out z = none ∧ picPolytope A b C γ 0 X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r} = ∅)) ≥
          1 - δ := by
  sorry

end QAlgorithms.Nannicini
