/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.MathlibImports

/-!
# Q23 (abstract part) — approximate strong duality for conic programs

The primal program is

  `maximize c x   subject to   x ∈ K,  A x = b`.

Here `K` is a convex cone in a real vector space `E`, `A : E → F` is linear and continuous,
and `F` is a locally convex Hausdorff space. A dual point is a linear functional `y` on `F`
with `c x ≤ y (A x)` for all `x ∈ K`. Its objective is `y b`.

**`conic_approx_duality`.** Let `V` bound the primal and suppose a primal feasible point
exists. Suppose also that the cone has a **coercive gauge** `μ`: a linear functional,
nonnegative on `K`, with compact truncations `K ∩ {μ ≤ R}`. Finally suppose `μ` is dominated
by a dual direction `y₊`, meaning `μ x ≤ y₊ (A x)` on `K`. Then for every `η > 0` there is a
dual point with objective `≤ V + η`.

The proof has two steps.

1. Apply Mathlib's Hahn–Banach separation, `geometric_hahn_banach_closed_point`. It separates
   the point `(b, V + η)` from the compact convex set `{(A x, c x) : x ∈ K, μ x ≤ R}`, which
   gives an approximate dual point. A primal feasible point forces the multiplier of the
   objective to be positive.
2. Repair the error with `y₊`. On `K` it is `≤ (a / R) μ`, and taking `R ≥ y₊ b` keeps the
   objective at most `V + η`.

No Slater hypothesis, duality theorem or solver output is assumed.
-/

namespace ShiQuantum

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Approximate strong duality for conic programs with a coercive gauge.** -/
theorem conic_approx_duality {K : Set E} (hKc : Convex ℝ K)
    (hKs : ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K)
    (A : E →ₗ[ℝ] F) (hA : Continuous A) (b : F) (c μ : E →ₗ[ℝ] ℝ) (hc : Continuous c)
    (hμ : ∀ x ∈ K, 0 ≤ μ x) (hcpt : ∀ R : ℝ, IsCompact (K ∩ {x | μ x ≤ R}))
    (yp : F →ₗ[ℝ] ℝ) (hyp : ∀ x ∈ K, μ x ≤ yp (A x))
    {V : ℝ} (hV : ∀ x ∈ K, A x = b → c x ≤ V) {xf : E} (hxf : xf ∈ K) (hAxf : A xf = b)
    {η : ℝ} (hη : 0 < η) :
    ∃ y : F →ₗ[ℝ] ℝ, (∀ x ∈ K, c x ≤ y (A x)) ∧ y b ≤ V + η := by
  set R : ℝ := max (max (μ xf) (yp b)) 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRxf : μ xf ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRyp : yp b ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  set KR : Set E := K ∩ {x | μ x ≤ R}
  have hKRc : Convex ℝ KR := hKc.inter (convex_halfSpace_le μ.isLinear R)
  set Φ : E →ₗ[ℝ] F × ℝ := A.prod c
  have hΦ : Continuous Φ := hA.prodMk hc
  set S : Set (F × ℝ) := Φ '' KR
  have hS : IsCompact S := (hcpt R).image hΦ
  have hSc : Convex ℝ S := hKRc.linear_image Φ
  have hp : (b, V + η) ∉ S := by
    rintro ⟨x, ⟨hxK, -⟩, hx⟩
    have h1 : A x = b := congrArg Prod.fst hx
    have h2 : c x = V + η := congrArg Prod.snd hx
    have := hV x hxK h1
    linarith
  obtain ⟨f, u, hfS, hfp⟩ := geometric_hahn_banach_closed_point hSc hS.isClosed hp
  set φ : F →ₗ[ℝ] ℝ := (f : F × ℝ →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ F ℝ)
  set lam : ℝ := f ((0 : F), (1 : ℝ))
  have hf : ∀ (v : F) (s : ℝ), f (v, s) = φ v + s * lam := by
    intro v s
    have e : ((v, s) : F × ℝ) = (v, (0 : ℝ)) + s • ((0 : F), (1 : ℝ)) := by
      ext <;> simp
    rw [e, map_add, map_smul, smul_eq_mul]
    rfl
  have hineq : ∀ x ∈ KR, φ (A x) + c x * lam < φ b + (V + η) * lam := by
    intro x hx
    have h1 := hfS (Φ x) ⟨x, hx, rfl⟩
    have h2 : Φ x = (A x, c x) := rfl
    rw [h2, hf] at h1
    rw [hf] at hfp
    linarith
  have hlam : 0 < lam := by
    have h := hineq xf ⟨hxf, hRxf⟩
    have := hV xf hxf hAxf
    rw [hAxf] at h
    by_contra hneg
    push Not at hneg
    nlinarith
  set z : F →ₗ[ℝ] ℝ := (-(1 / lam)) • φ
  have hz : ∀ v, z v * lam = -φ v := by
    intro v
    simp only [z, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  set a : ℝ := V + η - z b
  have hg : ∀ x ∈ KR, c x - z (A x) < a := by
    intro x hx
    have h := hineq x hx
    refine lt_of_mul_lt_mul_right ?_ hlam.le
    have e1 : (c x - z (A x)) * lam = c x * lam + φ (A x) := by rw [sub_mul, hz]; ring
    have e2 : a * lam = (V + η) * lam + φ b := by
      simp only [a]; rw [sub_mul, hz]; ring
    rw [e1, e2]
    linarith
  have h0K : (0 : E) ∈ K := by simpa using hKs xf hxf 0 le_rfl
  have ha : 0 < a := by
    have := hg 0 ⟨h0K, by simp only [Set.mem_ofPred_eq, map_zero]; linarith⟩
    simpa using this
  have hbound : ∀ x ∈ K, c x - z (A x) ≤ a / R * μ x := by
    intro x hx
    have hsm : ∀ t : ℝ, c (t • x) - z (A (t • x)) = t * (c x - z (A x)) := by
      intro t; rw [map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_sub]
    rcases (hμ x hx).eq_or_lt with h | h
    · rw [← h, mul_zero]
      by_contra hpos
      push Not at hpos
      have hmem := hg ((a / (c x - z (A x))) • x)
        ⟨hKs x hx _ (div_nonneg ha.le hpos.le), by
          simp only [Set.mem_ofPred_eq, map_smul, ← h, smul_eq_mul, mul_zero]; linarith⟩
      rw [hsm, div_mul_cancel₀ _ hpos.ne'] at hmem
      exact lt_irrefl _ hmem
    · have hmem := hg ((R / μ x) • x)
        ⟨hKs x hx _ (div_nonneg (by linarith) h.le), by
          simp only [Set.mem_ofPred_eq, map_smul, smul_eq_mul]
          rw [div_mul_cancel₀ _ h.ne']⟩
      rw [hsm] at hmem
      have hR0 : 0 < R := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hR0]
      rw [div_mul_eq_mul_div, div_lt_iff₀ h] at hmem
      linarith
  have hR0 : 0 < R := by linarith
  refine ⟨z + (a / R) • yp, fun x hx => ?_, ?_⟩
  · have h1 := hbound x hx
    have h2 : a / R * μ x ≤ a / R * yp (A x) :=
      mul_le_mul_of_nonneg_left (hyp x hx) (div_nonneg ha.le hR0.le)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linarith
  · have h1 : a / R * yp b ≤ a := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hR0]
      exact mul_le_mul_of_nonneg_left hRyp ha.le
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [a] at h1 ⊢
    linarith

end ShiQuantum
