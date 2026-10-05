/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.UhlmannGeneral

/-!
# Q12 — the two-target fidelity inequality

For density operators `ρ, σ, τ`:

  `fidelity ρ σ ^ 2 + fidelity ρ τ ^ 2 ≤ 1 + fidelity σ τ`   (`fidelity_two_targets`).

Only this upper bound is proved; no optimizer or protocol hypothesis is involved.

1. `two_overlaps_le`: for unit vectors `u, v, w` in any complex inner product space,
   `‖⟪w, u⟫‖² + ‖⟪w, v⟫‖² ≤ 1 + ‖⟪u, v⟫‖`. This is the norm bound `1 + ‖⟪u, v⟫‖` for the sum of
   the two rank-one projections onto `u` and `v`, evaluated at `w`. Proof: for
   `s = ⟪u,w⟫ u + ⟪v,w⟫ v`, the quantity `t = ‖⟪u,w⟫‖² + ‖⟪v,w⟫‖²` equals `⟪w, s⟫`, so `t ≤ ‖s‖`,
   and `‖s‖² ≤ t (1 + ‖⟪u,v⟫‖)`.
2. Fix the canonical purification `ψ` of `ρ`. Uhlmann (`uhlmann_attained`) gives purifications
   `φσ`, `φτ` of `σ`, `τ` with `⟪ψ, φσ⟫ = F(ρ,σ)` and `⟪ψ, φτ⟫ = F(ρ,τ)`.
3. Their mutual overlap is at most `F(σ,τ)` (`uhlmann_le`).
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

section Vectors

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Two rank-one projections**: `‖⟪w,u⟫‖² + ‖⟪w,v⟫‖² ≤ 1 + ‖⟪u,v⟫‖` for unit vectors. -/
theorem two_overlaps_le {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖⟪w, u⟫_ℂ‖ ^ 2 + ‖⟪w, v⟫_ℂ‖ ^ 2 ≤ 1 + ‖⟪u, v⟫_ℂ‖ := by
  set α := ⟪u, w⟫_ℂ
  set β := ⟪v, w⟫_ℂ
  set c := ⟪u, v⟫_ℂ
  rw [norm_inner_symm w u, norm_inner_symm w v]
  set t := ‖α‖ ^ 2 + ‖β‖ ^ 2
  set s := α • u + β • v
  have hwu : ⟪w, u⟫_ℂ = (starRingEnd ℂ) α := (inner_conj_symm w u).symm
  have hwv : ⟪w, v⟫_ℂ = (starRingEnd ℂ) β := (inner_conj_symm w v).symm
  have h1 : ⟪w, s⟫_ℂ = (t : ℂ) := by
    simp only [s, inner_add_right, inner_smul_right, hwu, hwv, Complex.mul_conj', t]
    push_cast; ring
  have ht0 : 0 ≤ t := by positivity
  have h2 : t ≤ ‖s‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) w s
    rw [h1, hw, one_mul, Complex.norm_real, Real.norm_of_nonneg ht0] at this
    exact this
  have h3 : ‖s‖ ^ 2 ≤ t + 2 * (‖α‖ * ‖β‖ * ‖c‖) := by
    have e := norm_add_sq (𝕜 := ℂ) (α • u) (β • v)
    rw [norm_smul, norm_smul, hu, hv, mul_one, mul_one] at e
    have hre : RCLike.re ⟪α • u, β • v⟫_ℂ ≤ ‖α‖ * ‖β‖ * ‖c‖ := by
      calc RCLike.re ⟪α • u, β • v⟫_ℂ ≤ ‖⟪α • u, β • v⟫_ℂ‖ := RCLike.re_le_norm _
        _ = ‖α‖ * ‖β‖ * ‖c‖ := by
          rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj]
          ring
    change ‖α • u + β • v‖ ^ 2 ≤ _
    rw [e]
    linarith
  have h4 : 2 * (‖α‖ * ‖β‖) ≤ t := by nlinarith [sq_nonneg (‖α‖ - ‖β‖)]
  have h5 : ‖s‖ ^ 2 ≤ t * (1 + ‖c‖) := by nlinarith [norm_nonneg c]
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have htpos : 0 < t := by linarith [norm_nonneg c]
  nlinarith [norm_nonneg s]

end Vectors

variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem norm_toE_eq_one_of_purification {E : Type} [Fintype E] {ψ : n × E → ℂ}
    {ρ : Matrix n n ℂ} (hψ : IsPurification ψ ρ) (hρ : IsDensity ρ) : ‖toE ψ‖ = 1 :=
  (isDensity_pure_iff_norm ψ).mp (hψ.isDensity hρ)

/-- **The two-target fidelity inequality.** -/
theorem fidelity_two_targets {ρ σ τ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hτ : IsDensity τ) :
    fidelity ρ σ ^ 2 + fidelity ρ τ ^ 2 ≤ 1 + fidelity σ τ := by
  obtain ⟨φσ, hφσ, hovσ⟩ := uhlmann_attained hρ.posSemidef hσ.posSemidef
  obtain ⟨φτ, hφτ, hovτ⟩ := uhlmann_attained hρ.posSemidef hτ.posSemidef
  have hψ := purify_isPurification hρ.posSemidef
  have key := two_overlaps_le (norm_toE_eq_one_of_purification hφσ hσ)
    (norm_toE_eq_one_of_purification hφτ hτ) (norm_toE_eq_one_of_purification hψ hρ)
  rw [inner_toE, inner_toE, inner_toE, hovσ, hovτ, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (fidelity_nonneg _ _), Real.norm_of_nonneg (fidelity_nonneg _ _)] at key
  have hστ := uhlmann_le hσ.posSemidef hτ.posSemidef hφσ hφτ
  linarith

end ShiQuantum
