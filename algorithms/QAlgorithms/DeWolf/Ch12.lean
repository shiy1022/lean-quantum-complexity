import QAlgorithms.Defs.Adversary

/-!
# de Wolf, Chapter 12: quantum algorithms from the generalized adversary bound

R. de Wolf, *Quantum Computing: Lecture Notes*, §12.1–§12.3 (PDF pp. 111–116).

Setting (p. 111): `f : D → {0,1}` with `D ⊆ {0,1}^N` (here `D : Finset (Fin N → Bool)`, only the
values of `f` on `D` are read). A `T`-query algorithm is `U_T O_x U_{T−1} ⋯ U_1 O_x U_0` applied
to a fixed start state, with input-independent unitaries and the standard query
`O_x : |i, b⟩ ↦ |i, b ⊕ x_i⟩` (`QueryAlg`, `xorOracle`); its output is a function `out` of the
computational-basis measurement outcome. `|ψ_x^t⟩` is `A.stateAt (xorOracle x) t`. An adversary
matrix (`IsAdversaryMatrix`) is a real symmetric `|D| × |D|` matrix with `Γ_xy = 0` whenever
`f(x) = f(y)`; `‖·‖` is the operator norm (`specNorm`); `Γ_i` is `maskMatrix Γ i`. The progress
measure `S_t = Σ_{x,y} Γ_xy α_x^* α_y ⟨ψ_x^t|ψ_y^t⟩` is `progressMeasure A Γ α t`.

§12.3 (pp. 114–116): the objects `t^±_x`, `ψ_y`, `Λ`, `Π_x`, `U_x = (2Π_x − I)(2Λ − I)` built from
a dual solution `(u, v)` are the fields of `AdvAlg` (`tPlus`, `tMinus`, `psi`, `lambdaSpace`,
`piSpace`, `walk`), whose `A` is the objective value of `(u, v)`.
-/

namespace QAlgorithms.DeWolf

/-- de Wolf §12.1, Claim 1 (PDF p. 112): let `A` be a `T`-query algorithm that computes
`f : D → {0,1}` with error probability at most `ε < 1/2` on every `x ∈ D`, let `Γ` be an adversary
matrix for `f` and `α` a unit vector of weights on `D`. Then the final progress measure satisfies
`|S_T| ≤ 2 √(ε(1−ε)) ‖Γ‖`. -/
theorem adversary_claim1_final_progress {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (f : (Fin N → Bool) → Bool) (D : Finset (Fin N → Bool)) (Γ : Matrix D D ℝ)
    (hΓ : IsAdversaryMatrix f D Γ) (α : D → ℂ) (hα : ∑ x : D, ‖α x‖ ^ 2 = 1) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (A : QueryAlg (Fin N) Bool W T)
    (out : (Fin N × Bool) × W → Bool) (hA : A.ComputesWithError out D f ε) :
    ‖progressMeasure A Γ α (Fin.last T)‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) * specNorm Γ := by
  sorry

/-- de Wolf §12.1, Claim 2 (PDF p. 112): for a `T`-query algorithm `A`, an adversary matrix `Γ`
for `f` and a unit vector `α` of weights on `D`, one query changes the progress measure by at most
twice the largest operator norm of the masked matrices `Γ_i` (`Γ` with `Γ_xy` set to `0` when
`x_i = y_i`): for all `t ∈ {0, …, T−1}`, `|S_t − S_{t+1}| ≤ 2 max_{i ∈ [N]} ‖Γ_i‖`. -/
theorem adversary_claim2_one_query {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (f : (Fin N → Bool) → Bool) (D : Finset (Fin N → Bool)) (Γ : Matrix D D ℝ)
    (hΓ : IsAdversaryMatrix f D Γ) (α : D → ℂ) (hα : ∑ x : D, ‖α x‖ ^ 2 = 1)
    (A : QueryAlg (Fin N) Bool W T) (t : Fin T) :
    ‖progressMeasure A Γ α t.castSucc - progressMeasure A Γ α t.succ‖ ≤
      2 * maxMaskedNorm Γ := by
  sorry

/-- de Wolf §12.1, Theorem 2 (generalized adversary bound, Høyer–Lee–Špalek; PDF p. 112): let
`f : D → {0,1}` with `D ⊆ {0,1}^N` and let `Γ` be an adversary matrix for `f`. Every `T`-query
algorithm (any workspace, any output rule) that computes `f` with worst-case error probability at
most `ε < 1/2` satisfies `T ≥ (1/2 − √(ε(1−ε))) ‖Γ‖ / max_{i ∈ [N]} ‖Γ_i‖`. When
`max_i ‖Γ_i‖ = 0` the matrix `Γ` is zero and the bound reads `T ≥ 0` (Lean's `x / 0 = 0`). -/
theorem generalized_adversary_bound {N : ℕ} (f : (Fin N → Bool) → Bool)
    (D : Finset (Fin N → Bool)) (Γ : Matrix D D ℝ) (hΓ : IsAdversaryMatrix f D Γ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (out : (Fin N × Bool) × W → Bool)
    (hA : A.ComputesWithError out D f ε) :
    (1 / 2 - Real.sqrt (ε * (1 - ε))) * specNorm Γ / maxMaskedNorm Γ ≤ (T : ℝ) := by
  sorry

/-- de Wolf §12.3 (PDF pp. 114–116), the generalized adversary bound upper-bounds quantum query
complexity: there is an absolute constant `C > 0` such that for every `N ≥ 1`, every
`f : D → {0,1}` with `D ⊆ {0,1}^N`, and every feasible solution `{u_xj, v_xj}` (of any dimension
`d`) of the dual SDP for `ADV±(f)` with objective value at most `A`, where `A ≥ 1`, there is a
query algorithm with at most `C · A` queries that computes `f` with error probability at most
`1/3` on every `x ∈ D`. "Small error probability" is the notes' bounded-error convention; the
assumption `A ≥ 1` is the source's "we may assume A ≥ 1" (p. 116). -/
theorem dual_adversary_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (D : Finset (Fin N → Bool))
      (f : (Fin N → Bool) → Bool) (d : ℕ) (u v : D → Fin N → EuclideanSpace ℂ (Fin d)) (A : ℝ),
      DualFeasibleDeWolf f D d u v → (dewolfDualObjective u v : ℝ) ≤ A → 1 ≤ A →
        ∃ (m T : ℕ) (alg : QueryAlg (Fin N) Bool (Fin m) T)
          (out : (Fin N × Bool) × Fin m → Bool),
          (T : ℝ) ≤ C * A ∧ alg.ComputesWithError out D f (1 / 3) := by
  sorry

/-- de Wolf §12.3, Claim 3 (PDF p. 115): for a feasible dual solution with objective value
`A > 0` and every `x ∈ D`, the state `|t^+_x⟩` is within Euclidean distance `0.01` of a
(nonzero, not necessarily normalized) eigenvector `|ϕ⟩` of `U_x = (2Π_x − I)(2Λ − I)` with
eigenvalue `1`. The constant `0.01` is the one the source's proof gives. -/
theorem adversary_claim3_tPlus_near_fixed {N : ℕ} (P : AdvAlg N)
    (hfeas : DualFeasibleDeWolf P.f P.D P.d P.u P.v) (hA : 0 < P.A) (x : P.D) :
    ∃ φ : AdvSpace N P.d, φ ≠ 0 ∧ P.walk x φ = φ ∧ ‖φ - P.tPlus x‖ ≤ 1 / 100 := by
  sorry

/-- de Wolf §12.3, Claim 4 (PDF pp. 115–116): for a feasible dual solution with objective value
`A > 0` and every `x ∈ D`, the state `|t^-_x⟩` is within Euclidean distance
`1/20 + 1/(2000A)` of a superposition of eigenvectors of `U_x` whose eigenvalues `e^{iθ}`,
`θ ∈ (−π, π]`, have `|θ| > Θ = 1/(1000A)`. The distance bound is the one the source's proof
establishes. -/
theorem adversary_claim4_tMinus_near_large_phase {N : ℕ} (P : AdvAlg N)
    (hfeas : DualFeasibleDeWolf P.f P.D P.d P.u P.v) (hA : 0 < P.A) (x : P.D) :
    ∃ φ ∈ (⨆ μ ∈ {μ : ℂ | 1 / (1000 * P.A) < |Complex.arg μ|},
        Module.End.eigenspace
          ((P.walk x : AdvSpace N P.d →L[ℂ] AdvSpace N P.d) : AdvSpace N P.d →ₗ[ℂ] AdvSpace N P.d)
          μ),
      ‖P.tMinus x - φ‖ ≤ 1 / 20 + 1 / (2000 * P.A) := by
  sorry

end QAlgorithms.DeWolf
