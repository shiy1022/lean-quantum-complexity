import QAlgorithms.Defs.SpectralFilter

/-!
# Lin–Tong, *Optimal polynomial based quantum eigenstate filtering with application to solving
quantum linear systems* (arXiv:1910.14596v4)

Cited "LT p.N" (PDF pages). Theorem 3 (p.8, eigenstate filtering) and the three properties of
the filtering polynomial in Lemma 2 (p.8, proved in Appendix E, pp.30–31).

Model (§2, p.5, Eq. (1)). `N = 2^n`; an `(m + n)`-qubit unitary `U` is an `(α, m, ε)`-block-encoding
of the `n`-qubit operator `A` if `‖A − α(⟨0^m| ⊗ I) U (|0^m⟩ ⊗ I)‖ ≤ ε` (operator norm, ancilla
register first): the frozen `IsQubitBlockEncoding m n U α ε A`. The filtering polynomial
`R_ℓ(x; Δ) = T_ℓ(−1 + 2(x² − Δ²)/(1 − Δ²)) / T_ℓ(−1 + 2(−Δ²)/(1 − Δ²))` (p.7) is the frozen
`chebFilterPoly ℓ Δ`; `D_Δ = [−1, −Δ] ∪ [Δ, 1]` (p.6) is `{x | Δ ≤ |x| ∧ |x| ≤ 1}`.
-/

namespace QAlgorithms.Papers.LinTong20Filter

open QAlgorithms

/-- **LT Theorem 3** (PDF p.8), eigenstate filtering.

Let `H` be a Hermitian matrix and `U_H` an `(α, m, 0)`-block-encoding of `H`. If `λ` is an
eigenvalue of `H` separated from the rest of the spectrum by a gap `Δ`, then one can construct a
`(1, m + 2, ε)`-block-encoding of the spectral projector `P_λ` (onto the `λ`-eigenspace, possibly
degenerate) using `O((α/Δ) log(1/ε))` applications of (controlled-) `U_H` and `U_H†` and
`O((mα/Δ) log(1/ε))` other primitive quantum gates.

Encoding choices.
* The circuit is chosen from the known data `n, m, α, Δ, λ, ε` only, before `H` and `U_H`
  (trap Q2; §3, p.7: "a known eigenvalue λ"); `U_H` enters only as the oracle of an
  `OracleCircuit`, whose `queryCount` counts every application (plain or controlled, `U_H` or
  `U_H†`; trap Q6).
* The circuit acts on exactly `m + 2 + n` wires, ancillas first: the `m + 2` ancillas of the
  produced encoding and the `n` system qubits, no further workspace.
* "Primitive quantum gates" is not fixed by the source; the frozen `twoQubitGateSet` (all
  two-qubit unitaries) is used: the construction needs arbitrary-angle rotations (p.6: phase
  factors "given and computed without error").
* `O(·)` constants: one absolute `C > 0` and one absolute threshold `ε₀ ∈ (0, 1)`, quantified
  before everything (trap 8); the bound is an `ε → 0` statement (as `ε → 1`, `log(1/ε) → 0`).
* The gap: `λ` is an eigenvalue of `H` and every eigenvalue `μ ≠ λ` has `|μ − λ| ≥ Δ`
  (frozen `IsGapSeparatedEigenvalue`); `Δ > 0`, and `α > 0` (Appendix A, p.26).

**Correction** (trap 30). Printed: `O((mα/Δ) log(1/ε))` other gates. Changed: `(m + 1)` in place
of `m`. Why: at `m = 0` the printed bound forces zero gates, while the source's own Theorem 1'
(p.6), on which the proof rests, gives `O((m + 1)ℓ)` gates. -/
theorem eigenstateFiltering :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ (n m : ℕ) (α Δ lam ε : ℝ), 0 < α → 0 < Δ → 0 < ε → ε ≤ ε₀ →
        ∃ c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => m + n) (m + 2 + n),
          (c.queryCount 0 : ℝ) ≤ C * (α / Δ) * Real.log (1 / ε) ∧
          (c.gateCount : ℝ) ≤ C * ((m : ℝ) + 1) * (α / Δ) * Real.log (1 / ε) ∧
          ∀ (H : Matrix (Qubits n) (Qubits n) ℂ) (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ),
            H.IsHermitian → IsQubitBlockEncoding m n UH α 0 H →
            IsGapSeparatedEigenvalue H lam Δ →
            IsQubitBlockEncoding (m + 2) n (c.unitary fun _ => UH) 1 ε
              (spectralProjector H lam) := by
  sorry

/-- **LT Lemma 2 (i)** (PDF p.8; proof in Appendix E, pp.30–31, where `0 < Δ < 1`).

`R_ℓ(x; Δ)` solves the minimax problem `minimize_{p ∈ P_{2ℓ}[x], p(0) = 1} max_{x ∈ D_Δ} |p(x)|`:
`R_ℓ` is a real polynomial of degree at most `2ℓ` with `R_ℓ(0) = 1`, and for every real
polynomial `p` of degree at most `2ℓ` with `p(0) = 1`, `max_{D_Δ} |R_ℓ| ≤ max_{D_Δ} |p|`.

Encoding: the comparison of maxima over the compact set `D_Δ` is stated without `sSup`: every
bound `M` of `|p|` on `D_Δ` also bounds `|R_ℓ|` on `D_Δ`. -/
theorem chebFilterPoly_minimax (ℓ : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    (chebFilterPoly ℓ Δ).natDegree ≤ 2 * ℓ ∧ (chebFilterPoly ℓ Δ).eval 0 = 1 ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * ℓ → p.eval 0 = 1 →
        ∀ M : ℝ, (∀ x : ℝ, Δ ≤ |x| → |x| ≤ 1 → |p.eval x| ≤ M) →
          ∀ x : ℝ, Δ ≤ |x| → |x| ≤ 1 → |(chebFilterPoly ℓ Δ).eval x| ≤ M := by
  sorry

/-- **LT Lemma 2 (ii)** (PDF p.8; proof in Appendix E, p.31).

For `0 < Δ ≤ 1/√12`: `|R_ℓ(x; Δ)| ≤ 2 e^{−√2 ℓ Δ}` for all `x ∈ D_Δ`, and `R_ℓ(0; Δ) = 1`. -/
theorem chebFilterPoly_decay (ℓ : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1 / Real.sqrt 12) :
    (∀ x : ℝ, Δ ≤ |x| → |x| ≤ 1 →
      |(chebFilterPoly ℓ Δ).eval x| ≤ 2 * Real.exp (-(Real.sqrt 2 * ℓ * Δ))) ∧
      (chebFilterPoly ℓ Δ).eval 0 = 1 := by
  sorry

/-- **LT Lemma 2 (iii)** (PDF p.8; proof in Appendix E, p.31, where `0 < Δ < 1`).

`|R_ℓ(x; Δ)| ≤ 1` for all `|x| ≤ 1`. -/
theorem chebFilterPoly_bounded (ℓ : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∀ x : ℝ, |x| ≤ 1 → |(chebFilterPoly ℓ Δ).eval x| ≤ 1 := by
  sorry

end QAlgorithms.Papers.LinTong20Filter
