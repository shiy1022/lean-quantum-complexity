import QAlgorithms.Defs.Walk

/-!
# Childs, Chapter 18: Discrete-time quantum walk

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 18 (PDF pp. 89–94).
-/

namespace QAlgorithms.Childs

/-- **Childs, Theorem 18.1** (PDF p. 91, proof pp. 91–92; definitions §18.2, p. 90). Fix an
`N × N` stochastic matrix `P`, and let `D` be the `N × N` matrix with entries
`D_jk = √(P_jk P_kj)` (`discriminant P`). Then the eigenvalues of the discrete-time quantum walk
`U = S(2Π − 1)` corresponding to `P` (`szegedyWalk P`) are `±1` and `λ ± i√(1 − λ²)`
(`= e^{± i arccos λ}`), where `λ` ranges over the eigenvalues of `D`.

Standing conventions of §18.2 (p. 90): `P_kj` is the probability of a transition to `k` from `j`,
and stochastic means nonnegative entries with `∑_k P_kj = 1` for every `j` (`IsColumnStochastic`);
`|ψ_j⟩ = ∑_k √P_kj |j, k⟩` (`szegedyState`), `Π = ∑_j |ψ_j⟩⟨ψ_j|` (`szegedyProj`),
`S = ∑_{j,k} |j, k⟩⟨k, j|` (`swapOp`), `U = S(2Π − 1)` (`szegedyWalk`).

The statement is read as two clauses: (1) every eigenvalue of `U` is `1`, `−1`, or
`λ ± i√(1 − λ²)` for an eigenvalue `λ` of `D`; (2) for every eigenvalue `λ` of `D`, both
`λ + i√(1 − λ²)` and `λ − i√(1 − λ²)` are eigenvalues of `U` (the proof's eigenvectors
`|λ̃⟩ − μ S|λ̃⟩`). The values `±1` are a containment only: for `N = 1`, `P = (1)`, `U = (1)` has
no eigenvalue `−1`. -/
theorem szegedyWalk_spectrum {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hP : IsColumnStochastic P) :
    (∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (szegedyWalk P)) μ →
      μ = 1 ∨ μ = -1 ∨
        ∃ l : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (discriminant P)) l ∧
          (μ = (l : ℂ) + Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ) ∨
            μ = (l : ℂ) - Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ))) ∧
    (∀ l : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (discriminant P)) l →
      Module.End.HasEigenvalue (Matrix.toLin' (szegedyWalk P))
          ((l : ℂ) + Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ)) ∧
        Module.End.HasEigenvalue (Matrix.toLin' (szegedyWalk P))
          ((l : ℂ) - Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ))) := by
  sorry

/-- **Childs, Lemma 18.2** (PDF p. 93; setting §18.4, p. 92). If the second largest eigenvalue of
`P` (in absolute value) is at most `1 − δ` and `|M| ≥ ϵN`, then `‖P_M‖ ≤ 1 − δϵ`.

Standing assumptions of §18.4 (p. 92): `P` is an `N × N` stochastic matrix (column sums `1`,
nonnegative entries, `IsColumnStochastic`), and "from now on the original walk `P` is symmetric"
(for a real matrix, Hermitian = symmetric); `M ⊆ V = Fin N` is the marked set, and `P_M` is `P`
with the rows and columns of the vertices in `M` deleted (`unmarkedSubmatrix P M`, eq. (18.36)).
`‖·‖` is the spectral norm (`specNorm`).

"The second largest eigenvalue in absolute value is at most `1 − δ`": listing the eigenvalues
of `P` with multiplicity (`hsymm.eigenvalues`), at most one of them has absolute value
`> 1 − δ`. `N ≥ 2` because the source speaks of a second eigenvalue; `δ > 0` and `ϵ > 0`
because they are a spectral gap and a marked fraction (with negative `δ, ϵ` and `M = ∅` the
conclusion `1 ≤ 1 − δϵ` fails). -/
theorem unmarked_specNorm_le {N : ℕ} (hN : 2 ≤ N) (P : Matrix (Fin N) (Fin N) ℝ)
    (hP : IsColumnStochastic P) (hsymm : P.IsHermitian) (M : Finset (Fin N)) (δ ϵ : ℝ)
    (hδ : 0 < δ) (hϵ : 0 < ϵ)
    (hgap : (Finset.univ.filter fun i : Fin N => 1 - δ < |hsymm.eigenvalues i|).card ≤ 1)
    (hM : ϵ * (N : ℝ) ≤ (M.card : ℝ)) :
    specNorm (unmarkedSubmatrix P M) ≤ 1 - δ * ϵ := by
  sorry

end QAlgorithms.Childs
