/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.PadMessages

/-!
# Q30 — unitary provers

Every isometric prover has a prover on one fixed memory `N = Σ k, M k` whose turns are
unitaries and whose runs are the original runs, embedded (**`exists_unitary_prover`**).

* `exists_unitary_ext`: an isometry `V` agrees with a unitary on the range of any isometry `J`.
* `dilateU` (turns `dilU`, unitary by `dilU_mem`), `pureRun_dilateU`, `accept_dilateU`.
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-- **Unitary extension.** Two isometries with the same domain differ by a unitary. -/
theorem exists_unitary_ext {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (J V : Matrix B A ℂ) (hJ : Jᴴ * J = 1) (hV : Vᴴ * V = 1) :
    ∃ U ∈ Matrix.unitaryGroup B ℂ, U * J = V := by
  obtain ⟨U, hU, h⟩ := exists_unitary_of_mul_conjTranspose_eq (M := Jᴴ) (N := Vᴴ)
    (by rw [conjTranspose_conjTranspose, conjTranspose_conjTranspose, hJ, hV])
  refine ⟨Uᴴ, Unitary.star_mem hU, ?_⟩
  have := congrArg conjTranspose h
  rw [conjTranspose_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose] at this
  exact this.symm

variable {d : Desc} (T : IsoStrategy (Reg d) (Reg d) d.numMsgs)

variable (d) in
/-- The common memory. -/
abbrev DilMem : Type := Σ k : Fin (d.numMsgs + 1), T.M k

/-- The embedding of memory `k`. -/
def ιM {k : ℕ} (hk : k ≤ d.numMsgs) (μ : T.M k) : DilMem d T := ⟨⟨k, by omega⟩, μ⟩

theorem ιM_injective {k : ℕ} (hk : k ≤ d.numMsgs) : Function.Injective (ιM T hk) := by
  intro a b h
  simp only [ιM, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-- The embedding matrix of memory `k`, with a register `R` alongside. -/
noncomputable def embM {R : Type} [DecidableEq R] {k : ℕ} (hk : k ≤ d.numMsgs) :
    Matrix (R × DilMem d T) (R × T.M k) ℂ :=
  Matrix.of fun p q => if p = (q.1, ιM T hk q.2) then 1 else 0

theorem embM_iso {R : Type} [Fintype R] [DecidableEq R] {k : ℕ} (hk : k ≤ d.numMsgs) :
    (embM T (R := R) hk)ᴴ * embM T (R := R) hk = 1 := by
  ext ⟨r, μ⟩ ⟨r', μ'⟩
  simp only [mul_apply, conjTranspose_apply, embM, of_apply, one_apply]
  rw [Finset.sum_eq_single (r, ιM T hk μ)]
  · simp only [if_true, star_one, one_mul, Prod.mk.injEq]
    by_cases h1 : r = r' <;> by_cases h2 : μ = μ' <;>
      simp [h1, h2, (ιM_injective T hk).eq_iff, eq_comm]
  · intro p _ hp
    rw [if_neg hp, star_zero, zero_mul]
  · simp

/-- The turns, embedded: `embM (k+1) * V k`. -/
theorem embV_iso {k : ℕ} (hk : k < d.numMsgs) :
    (embM T (R := Reg d k) (k := k + 1) hk * T.V k)ᴴ * (embM T (R := Reg d k) (k := k + 1) hk * T.V k) = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (embM T _)ᴴ, embM_iso, Matrix.one_mul,
    T.V_iso k hk]

/-- The unitary turns. -/
noncomputable def dilU (k : ℕ) : Matrix (Reg d k × DilMem d T) (Reg d k × DilMem d T) ℂ :=
  if hk : k < d.numMsgs then
    Classical.choose (exists_unitary_ext (embM T (R := Reg d k) (k := k) hk.le)
      (embM T (R := Reg d k) (k := k + 1) hk * T.V k) (embM_iso T hk.le) (embV_iso T hk))
  else 1

theorem dilU_mem {k : ℕ} : dilU T k ∈ Matrix.unitaryGroup (Reg d k × DilMem d T) ℂ := by
  unfold dilU
  split_ifs with hk
  · exact (Classical.choose_spec (exists_unitary_ext _ _ (embM_iso T hk.le) (embV_iso T hk))).1
  · exact Submonoid.one_mem _

theorem dilU_embM {k : ℕ} (hk : k < d.numMsgs) :
    dilU T k * embM T (R := Reg d k) hk.le = embM T (R := Reg d k) (k := k + 1) hk * T.V k := by
  unfold dilU
  rw [dif_pos hk]
  exact (Classical.choose_spec (exists_unitary_ext _ _ (embM_iso T hk.le) (embV_iso T hk))).2

/-- **The unitary prover.** -/
@[reducible] noncomputable def dilateU : IsoStrategy (Reg d) (Reg d) d.numMsgs where
  M _ := DilMem d T
  init := fun ν => ∑ μ, (if ν = ιM T (Nat.zero_le _) μ then 1 else 0) * T.init μ
  init_density := by
    have : (fun ν => ∑ μ, (if ν = ιM T (Nat.zero_le _) μ then (1 : ℂ) else 0) * T.init μ) =
        (Matrix.of fun ν μ => if ν = ιM T (Nat.zero_le _) μ then (1 : ℂ) else 0) *ᵥ T.init := by
      funext ν; simp [mulVec, dotProduct]
    rw [this, pureState_mulVec]
    refine (isChannel_conjMap ?_).map_density T.init_density
    ext μ μ'
    simp only [mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [Finset.sum_eq_single (ιM T (Nat.zero_le _) μ)]
    · simp only [if_true, star_one, one_mul]
      by_cases h : μ = μ'
      · subst h; simp
      · rw [if_neg (fun e => h (ιM_injective T _ e)),
          if_neg h]
    · intro ν _ hν; rw [if_neg hν, star_zero, zero_mul]
    · simp
  V k := dilU T k
  V_iso k _ := Matrix.mem_unitaryGroup_iff'.mp (dilU_mem T)

/-- Embed a memory vector. -/
noncomputable def embVec {k : ℕ} (hk : k ≤ d.numMsgs) {X : Type} (v : X × T.M k → ℂ) :
    X × DilMem d T → ℂ :=
  fun p => ∑ μ, (if p.2 = ιM T hk μ then 1 else 0) * v (p.1, μ)

theorem embVec_ι {k : ℕ} (hk : k ≤ d.numMsgs) {X : Type} (v : X × T.M k → ℂ) (x : X) (μ : T.M k) :
    embVec T hk v (x, ιM T hk μ) = v (x, μ) := by
  rw [embVec, Finset.sum_eq_single μ]
  · simp
  · intro μ' _ h; rw [if_neg (fun e => h (ιM_injective T hk e).symm), zero_mul]
  · simp

theorem embM_mulVec {R : Type} [Fintype R] [DecidableEq R] {k : ℕ} (hk : k ≤ d.numMsgs)
    (z : R × T.M k → ℂ) (g : R) (ν : DilMem d T) :
    (embM T (R := R) hk *ᵥ z) (g, ν) = ∑ μ, (if ν = ιM T hk μ then 1 else 0) * z (g, μ) := by
  simp only [mulVec, dotProduct, embM, of_apply, Fintype.sum_prod_type, Prod.mk.injEq]
  rw [Finset.sum_eq_single g]
  · simp
  · intro g' _ hg'; simp [Ne.symm hg']
  · simp

theorem turnVec_dilateU {k : ℕ} (hk : k < d.numMsgs) (v : Qubits d.totalWires × T.M k → ℂ) :
    turnVec (dilateU T) k (embVec T hk.le v) = embVec T (k := k + 1) hk (turnVec T k v) := by
  funext ⟨y, ν'⟩
  simp only [turnVec, Function.comp_apply]
  have hts : turnSplit d k (DilMem d T) (y, ν') =
      ((wireSplitE d k y).1, ((wireSplitE d k y).2, ν')) := rfl
  rw [hts, one_kron_mulVec_apply]
  have hw : (fun q : Reg d k × DilMem d T => embVec T hk.le v ((turnSplit d k (DilMem d T)).symm
      ((wireSplitE d k y).1, q))) = embM T hk.le *ᵥ fun q : Reg d k × T.M k =>
        v ((turnSplit d k (T.M k)).symm ((wireSplitE d k y).1, q)) := by
    funext ⟨g, ν⟩
    rw [embM_mulVec]
    rfl
  change (dilU T k *ᵥ fun q => embVec T hk.le v ((turnSplit d k (DilMem d T)).symm
    ((wireSplitE d k y).1, q))) _ = _
  rw [hw, mulVec_mulVec, dilU_embM T hk, ← mulVec_mulVec, embM_mulVec]
  simp only [embVec]
  refine Finset.sum_congr rfl fun μ' _ => ?_
  congr 1
  change _ = (((1 : Matrix (Rest d k) (Rest d k) ℂ) ⊗ₖ T.V k) *ᵥ
    (v ∘ (turnSplit d k (T.M k)).symm)) ((wireSplitE d k y).1, ((wireSplitE d k y).2, μ'))
  rw [one_kron_mulVec_apply]
  rfl

theorem mulVec_embSum {X M : Type} [Fintype X] [Fintype M] (B : Matrix X X ℂ) (c : M → ℂ)
    (f : X → M → ℂ) (y : X) :
    (B *ᵥ fun y' => ∑ μ, c μ * f y' μ) y = ∑ μ, c μ * (B *ᵥ fun y' => f y' μ) y := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun y' _ => by ring

/-- **The unitary prover runs the original prover, embedded.** -/
theorem pureRun_dilateU : ∀ k (hk : k ≤ d.numMsgs),
    pureRun (dilateU T) k = embVec T hk (pureRun T k)
  | 0, hk => by
    funext ⟨y, ν⟩
    rw [pureRun, pureRun, kronOne_mulVec_apply]
    simp only [embVec, kronOne_mulVec_apply]
    rw [← mulVec_embSum]
    congr 1
    funext y'
    change zeroVec _ y' * ∑ μ, (if ν = ιM T _ μ then 1 else 0) * T.init μ = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by ring
  | k + 1, hk => by
    funext ⟨y, ν⟩
    rw [pureRun, pureRun, pureRun_dilateU k (by omega), turnVec_dilateU T (by omega),
      kronOne_mulVec_apply]
    simp only [embVec, kronOne_mulVec_apply]
    rw [← mulVec_embSum]

theorem sum_norm_embVec {k : ℕ} (hk : k ≤ d.numMsgs) {X : Type} [Fintype X]
    (v : X × T.M k → ℂ) (x : X) :
    ∑ ν, ‖embVec T hk v (x, ν)‖ ^ 2 = ∑ μ, ‖v (x, μ)‖ ^ 2 := by
  have h1 : ∑ ν, ‖embVec T hk v (x, ν)‖ ^ 2 =
      ∑ ν ∈ Finset.univ.image (ιM T hk), ‖embVec T hk v (x, ν)‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun ν _ hν => ?_).symm
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hν
    have : embVec T hk v (x, ν) = 0 :=
      Finset.sum_eq_zero fun μ _ => by rw [if_neg (fun e => hν μ e.symm), zero_mul]
    rw [this, norm_zero]; norm_num
  rw [h1, Finset.sum_image fun a _ b _ h => ιM_injective T hk h]
  exact Finset.sum_congr rfl fun μ _ => by rw [embVec_ι]

/-- **The unitary prover has the same acceptance probability.** -/
theorem accept_dilateU : accept (dilateU T).toOp = accept T.toOp := by
  rw [accept_pureRun, accept_pureRun, accept_expect, accept_expect, pureRun_dilateU T _ le_rfl]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · exact sum_norm_embVec T le_rfl _ y
  · simp

end ShiQIP
