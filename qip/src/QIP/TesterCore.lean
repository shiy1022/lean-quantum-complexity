/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.StrategyRealization

/-!
# Q20 (core) — one prover turn in transition-vector form

Let `e : W ≃ Rr × Xx` split the verifier wires into the rest and a message register. For
`A : Matrix W H ℂ` (columns: verifier states indexed by histories `H`) and a prover state
`R` on `H × M`, the global state `(A ⊗ 1) R (A ⊗ 1)ᴴ` is mapped by the prover turn
`turnMap e Φ` (`Φ` on register × memory, the identity on the rest) to

  `(transfer e A ⊗ 1) · linkState Φ R · (transfer e A ⊗ 1)ᴴ`   (`turn_conj`),

where `transfer e A ((h, x), y)` is the column `A h` with `|y⟩⟨x|` inserted on the register, and
`linkState Φ R` is the link product `linkStep Φ R` re-associated. The proof is entry-wise. It
expands the blocks of the state in matrix units (`blockOf_expand`), uses linearity of `Φ`, and
applies the entry formula `linkStep_apply` of the link product.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-- The `(h, h')` memory block of a state on `H × M`. -/
def memBlock {H Mm : Type} (R : Matrix (H × Mm) (H × Mm) ℂ) (h h' : H) : Matrix Mm Mm ℂ :=
  Matrix.of fun m m' => R (h, m) (h', m')

/-- **Entries of the link product.** -/
theorem linkStep_apply {H Xx Mm Mm' : Type} [Fintype H] [Fintype Xx] [DecidableEq Xx]
    [Fintype Mm] (Φ : MatMap (Xx × Mm) (Xx × Mm')) (R : Matrix (H × Mm) (H × Mm) ℂ)
    (h h' : H) (x x' : Xx) (q q' : Xx × Mm') :
    linkStep Φ R ((h, x), q) ((h', x'), q') =
      Φ (Matrix.single x x' 1 ⊗ₖ memBlock R h h') q q' := by
  have hb : blockOf (Matrix.reindex (linkEquiv H Mm Xx) (linkEquiv H Mm Xx)
      (R ⊗ₖ vecMulVec (omegaVec Xx) (star (omegaVec Xx)))) (h, x) (h', x') =
      Matrix.single x x' 1 ⊗ₖ memBlock R h h' := by
    ext ⟨a, m⟩ ⟨b, m'⟩
    simp only [blockOf_apply, reindex_apply, submatrix_apply, linkEquiv, Equiv.coe_fn_symm_mk,
      kroneckerMap_apply, vecMulVec_apply, omegaVec, Pi.star_apply, single_apply, memBlock,
      of_apply]
    by_cases ha : x = a <;> by_cases hb : x' = b <;> simp [ha, hb, mul_comm]
  rw [linkStep, liftR_apply]
  exact congrArg (fun Z => Φ Z q q') hb

theorem star_ite_zero (p : Prop) [Decidable p] (a : ℂ) :
    star (if p then a else 0) = if p then star a else 0 := by
  split_ifs <;> simp

theorem kron_one_apply {V H Mm : Type} [DecidableEq Mm] (A : Matrix V H ℂ) (v : V) (h : H)
    (μ m : Mm) : (A ⊗ₖ (1 : Matrix Mm Mm ℂ)) (v, μ) (h, m) = if μ = m then A v h else 0 := by
  rw [kroneckerMap_apply, one_apply]; split_ifs <;> simp

/-- Entries of `(A ⊗ 1) R (A ⊗ 1)ᴴ`. -/
theorem conjKron_apply {V H Mm : Type} [Fintype H] [Fintype Mm] [DecidableEq Mm]
    (A : Matrix V H ℂ) (R : Matrix (H × Mm) (H × Mm) ℂ) (v v' : V) (μ μ' : Mm) :
    ((A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R * (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ) (v, μ) (v', μ') =
      ∑ h, ∑ h', A v h * R (h, μ) (h', μ') * star (A v' h') := by
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, kron_one_apply, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, star_ite_zero, mul_ite, mul_zero,
    Finset.sum_mul]
  have hc : ∀ h' : H, (∑ m' : Mm, ∑ h : H,
      if μ' = m' then A v h * R (h, μ) (h', m') * star (A v' h') else 0) =
      ∑ h, A v h * R (h, μ) (h', μ') * star (A v' h') := by
    intro h'
    rw [Finset.sum_eq_single μ']
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [hc]
  rw [Finset.sum_comm]

/-- Split the global system at a register: `W × M ≃ Rr × (Xx × M)`. -/
def splitE {W Rr Xx : Type} (e : W ≃ Rr × Xx) (Mm : Type) : W × Mm ≃ Rr × (Xx × Mm) :=
  (e.prodCongr (Equiv.refl Mm)).trans (Equiv.prodAssoc _ _ _)

/-- A prover turn: `Φ` on register × memory, the identity on the rest. -/
def turnMap {W Rr Xx Mm Mm' : Type} (e : W ≃ Rr × Xx) (Φ : MatMap (Xx × Mm) (Xx × Mm')) :
    MatMap (W × Mm) (W × Mm') :=
  reindexMap (splitE e Mm').symm ∘ₗ liftR Rr Φ ∘ₗ reindexMap (splitE e Mm)

/-- Insert `|y⟩⟨x|` on the register into the columns of `A`. -/
def transfer {W Rr Xx H : Type} [DecidableEq Xx] (e : W ≃ Rr × Xx) (A : Matrix W H ℂ) :
    Matrix W ((H × Xx) × Xx) ℂ :=
  Matrix.of fun w p => if (e w).2 = p.2 then A (e.symm ((e w).1, p.1.2)) p.1.1 else 0

/-- The link product, re-associated to `((H × X) × X) × M'`. -/
noncomputable def linkState {H Xx Mm Mm' : Type} [Fintype H] [Fintype Xx] [DecidableEq Xx]
    [Fintype Mm] (Φ : MatMap (Xx × Mm) (Xx × Mm')) (R : Matrix (H × Mm) (H × Mm) ℂ) :
    Matrix (((H × Xx) × Xx) × Mm') (((H × Xx) × Xx) × Mm') ℂ :=
  Matrix.reindex (Equiv.prodAssoc (H × Xx) Xx Mm').symm (Equiv.prodAssoc (H × Xx) Xx Mm').symm
    (linkStep Φ R)

theorem blockOf_expand {W Rr Xx H Mm : Type} [Fintype Xx] [DecidableEq Xx] [Fintype H]
    [Fintype Mm] [DecidableEq Mm] (e : W ≃ Rr × Xx) (A : Matrix W H ℂ)
    (R : Matrix (H × Mm) (H × Mm) ℂ) (r r' : Rr) :
    blockOf (((A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R * (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ).submatrix
      (splitE e Mm).symm (splitE e Mm).symm) r r' =
      ∑ h, ∑ h', ∑ x, ∑ x', (A (e.symm (r, x)) h * star (A (e.symm (r', x')) h')) •
        (Matrix.single x x' 1 ⊗ₖ memBlock R h h') := by
  ext ⟨x₁, m₁⟩ ⟨x₂, m₂⟩
  rw [blockOf_apply, submatrix_apply]
  change ((A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R * (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ)
    (e.symm (r, x₁), m₁) (e.symm (r', x₂), m₂) = _
  rw [conjKron_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply, Matrix.single_apply,
    memBlock, of_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  rw [Finset.sum_eq_single x₁, Finset.sum_eq_single x₂]
  · simp; ring
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun x' _ => ?_
    simp [hb]
  · simp

theorem sum_transfer_left {W Rr Xx H : Type} [Fintype Xx] [DecidableEq Xx] [Fintype H]
    (e : W ≃ Rr × Xx) (A : Matrix W H ℂ) (w : W) (g : (H × Xx) × Xx → ℂ) :
    ∑ p, transfer e A w p * g p = ∑ h, ∑ x, A (e.symm ((e w).1, x)) h * g ((h, x), (e w).2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (e w).2]
  · simp [transfer]
  · intro y _ hy; simp [transfer, Ne.symm hy]
  · simp

theorem sum_transfer_right {W Rr Xx H : Type} [Fintype Xx] [DecidableEq Xx] [Fintype H]
    (e : W ≃ Rr × Xx) (A : Matrix W H ℂ) (w : W) (g : (H × Xx) × Xx → ℂ) :
    ∑ p, g p * star (transfer e A w p) =
      ∑ h, ∑ x, g ((h, x), (e w).2) * star (A (e.symm ((e w).1, x)) h) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (e w).2]
  · simp [transfer]
  · intro y _ hy; simp [transfer, Ne.symm hy]
  · simp

/-- **One prover turn in transition-vector form.** -/
theorem turn_conj {W Rr Xx H Mm Mm' : Type} [Fintype W] [Fintype Rr] [Fintype Xx]
    [DecidableEq Xx] [Fintype H] [Fintype Mm] [DecidableEq Mm] [Fintype Mm'] [DecidableEq Mm']
    (e : W ≃ Rr × Xx) (A : Matrix W H ℂ) (R : Matrix (H × Mm) (H × Mm) ℂ)
    (Φ : MatMap (Xx × Mm) (Xx × Mm')) :
    turnMap e Φ ((A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R * (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ) =
      (transfer e A ⊗ₖ (1 : Matrix Mm' Mm' ℂ)) * linkState Φ R *
        (transfer e A ⊗ₖ (1 : Matrix Mm' Mm' ℂ))ᴴ := by
  ext ⟨w, μ⟩ ⟨w', μ'⟩
  rw [conjKron_apply]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_transfer_left]
  simp_rw [sum_transfer_right]
  simp only [turnMap, LinearMap.comp_apply, reindexMap_apply, reindex_apply, submatrix_apply,
    Equiv.symm_symm]
  rw [liftR_apply]
  have hs : ∀ (u : W) (ν : Mm'), (splitE e Mm') (u, ν) = ((e u).1, ((e u).2, ν)) :=
    fun _ _ => rfl
  rw [hs, hs]
  dsimp only
  rw [blockOf_expand]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← linkStep_apply, linkState, reindex_apply, submatrix_apply, Equiv.symm_symm,
    Equiv.prodAssoc_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun h' _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  ring

end ShiQIP
