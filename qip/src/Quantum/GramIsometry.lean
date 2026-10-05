/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.HilbertBridge

/-!
# Q09 (support) — families with equal Gram matrices

In a finite-dimensional complex inner product space `V`, two finite families `x, y : ι → V`
with equal Gram matrices (`⟪x i, x j⟫ = ⟪y i, y j⟫` for all `i, j`) are related by a linear
isometry of `V` (`exists_linearIsometry_of_inner_eq`).

Construction: `T c = ∑ i, c i • x i` and `S c = ∑ i, c i • y i` satisfy `‖T c‖ = ‖S c‖`. Hence
`ker T ≤ ker S`, so `S` factors through `range T ≅ (ι → ℂ) ⧸ ker T` as an isometry on
`range T`. Mathlib's `LinearIsometry.extend` extends it to all of `V`. No independence, rank or
full-rank assumption is made: the families may be linearly dependent, and some vectors may be
zero.
-/

namespace ShiQuantum

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℂ V] in
theorem inner_linearCombination (x : ι → V) (c : ι → ℂ) :
    ⟪Fintype.linearCombination ℂ x c, Fintype.linearCombination ℂ x c⟫_ℂ =
      ∑ i, ∑ j, star (c j) * c i * ⟪x j, x i⟫_ℂ := by
  simp only [Fintype.linearCombination_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def]
  ring

omit [FiniteDimensional ℂ V] in
theorem norm_linearCombination_eq {x y : ι → V} (h : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ)
    (c : ι → ℂ) :
    ‖Fintype.linearCombination ℂ x c‖ = ‖Fintype.linearCombination ℂ y c‖ := by
  have hi := inner_linearCombination x c
  rw [show (∑ i, ∑ j, star (c j) * c i * ⟪x j, x i⟫_ℂ) =
      ∑ i, ∑ j, star (c j) * c i * ⟪y j, y i⟫_ℂ by simp only [h],
    ← inner_linearCombination y c, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
  have : ‖Fintype.linearCombination ℂ x c‖ ^ 2 = ‖Fintype.linearCombination ℂ y c‖ ^ 2 := by
    exact_mod_cast hi
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- **Equal Gram matrices give a linear isometry.** -/
theorem exists_linearIsometry_of_inner_eq {x y : ι → V}
    (h : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ) : ∃ L : V →ₗᵢ[ℂ] V, ∀ i, L (x i) = y i := by
  classical
  set T := Fintype.linearCombination ℂ x
  set S := Fintype.linearCombination ℂ y
  have hn : ∀ c, ‖T c‖ = ‖S c‖ := norm_linearCombination_eq h
  have hker : LinearMap.ker T ≤ LinearMap.ker S := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, ← hn, hc, norm_zero]
  let L0 : LinearMap.range T →ₗ[ℂ] V :=
    (LinearMap.ker T).liftQ S hker ∘ₗ T.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ c, L0 ⟨T c, LinearMap.mem_range_self T c⟩ = S c := by
    intro c
    simp only [L0, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  let L1 : LinearMap.range T →ₗᵢ[ℂ] V :=
    { L0 with
      norm_map' := by
        rintro ⟨_, c, rfl⟩
        change ‖L0 ⟨T c, LinearMap.mem_range_self T c⟩‖ = ‖T c‖
        rw [hL0, hn] }
  refine ⟨L1.extend, fun i => ?_⟩
  have hxi : T (Pi.single i 1) = x i := by
    simp [T, Fintype.linearCombination_apply, Pi.single_apply]
  have hyi : S (Pi.single i 1) = y i := by
    simp [S, Fintype.linearCombination_apply, Pi.single_apply]
  have := L1.extend_apply ⟨T (Pi.single i 1), LinearMap.mem_range_self T _⟩
  simp only at this
  rw [← hxi, this, ← hyi]
  exact hL0 _

end ShiQuantum
