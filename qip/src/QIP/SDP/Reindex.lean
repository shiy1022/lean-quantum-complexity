/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.SDP.Product

/-!
# Relabelling message registers

Register-wise bijections `τX i : X i ≃ X' i`, `τY i : Y i ≃ Y' i` induce bijections of
histories `histMap τX τY k : Hist X Y k ≃ Hist X' Y' k`.

* `isStrategy_relabel`: relabelling a causal strategy along `histMap` gives a causal strategy,
  and conversely.
* **`sdpVal_relabel`**: the strategy value is invariant under relabelling:
  `sdpVal (T.submatrix (histMap …) (histMap …)) = sdpVal T`.

These lemmas let a verifier whose registers are merely *isomorphic* to products be compared
with the product game of `QIP.SDP.Product`.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Submatrices, partial traces and `⊗ 1` -/

theorem traceRight_submatrix_prodMap {α α' β β' : Type} [Fintype β] [Fintype β']
    (M : Matrix (α × β) (α × β) ℂ) (f f' : α' → α) (g : β' ≃ β) :
    traceRight (M.submatrix (Prod.map f g) (Prod.map f' g)) = (traceRight M).submatrix f f' := by
  ext a b
  simp only [traceRight_apply, submatrix_apply, Prod.map_apply]
  exact g.sum_comp (fun j => M (f a, j) (f' b, j))

theorem kron_one_submatrix {α α' β β' : Type} [DecidableEq β] [DecidableEq β']
    (A : Matrix α α ℂ) (f f' : α' → α) (g : β' ≃ β) :
    (A ⊗ₖ (1 : Matrix β β ℂ)).submatrix (Prod.map f g) (Prod.map f' g) =
      A.submatrix f f' ⊗ₖ (1 : Matrix β' β' ℂ) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  simp only [submatrix_apply, Prod.map_apply, kroneckerMap_apply, one_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-! ## Relabelled histories -/

variable {X Y X' Y' : ℕ → Type}
variable [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (X' i)] [∀ i, Fintype (Y' i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] [∀ i, DecidableEq (X' i)]
  [∀ i, DecidableEq (Y' i)]

/-- Histories along register-wise bijections. -/
def histMap (τX : ∀ i, X i ≃ X' i) (τY : ∀ i, Y i ≃ Y' i) :
    ∀ k, Hist X Y k ≃ Hist X' Y' k
  | 0 => Equiv.refl Unit
  | k + 1 => ((histMap τX τY k).prodCongr (τX k)).prodCongr (τY k)

/-- Relabel a family of matrices along `histMap`. -/
def relabel (τX : ∀ i, X i ≃ X' i) (τY : ∀ i, Y i ≃ Y' i)
    (Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ) : ∀ k, Matrix (Hist X' Y' k) (Hist X' Y' k) ℂ :=
  fun k => (Q k).submatrix (histMap τX τY k).symm (histMap τX τY k).symm

/-- **Relabelling preserves causal strategies.** -/
theorem isStrategy_relabel (τX : ∀ i, X i ≃ X' i) (τY : ∀ i, Y i ≃ Y' i) {r : ℕ}
    {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (hQ : IsStrategy r Q) :
    IsStrategy r (relabel τX τY Q) where
  zero := by
    ext a b
    have h := congrFun (congrFun hQ.zero ((histMap τX τY 0).symm a)) ((histMap τX τY 0).symm b)
    simp only [relabel, submatrix_apply]
    rw [h]
    obtain rfl : a = b := Subsingleton.elim (α := Unit) a b
    simp
  posSemidef k hk := (hQ.posSemidef k hk).submatrix _
  causal k hk := by
    have hc := hQ.causal k hk
    unfold Causal at hc ⊢
    have h1 := traceRight_submatrix_prodMap (α := Hist X Y k × X k) (β := Y k) (Q (k + 1))
      (Prod.map (histMap τX τY k).symm (τX k).symm) (Prod.map (histMap τX τY k).symm (τX k).symm)
      (τY k).symm
    rw [hc] at h1
    exact h1.trans (kron_one_submatrix _ _ _ (τX k).symm)

theorem relabel_relabel_symm (τX : ∀ i, X i ≃ X' i) (τY : ∀ i, Y i ≃ Y' i)
    (Q : ∀ k, Matrix (Hist X' Y' k) (Hist X' Y' k) ℂ) :
    relabel τX τY (relabel (fun i => (τX i).symm) (fun i => (τY i).symm) Q) = Q := by
  have h : ∀ k (h : Hist X' Y' k),
      (histMap (fun i => (τX i).symm) (fun i => (τY i).symm) k).symm
        ((histMap τX τY k).symm h) = h := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      rintro ⟨⟨h, x⟩, y⟩
      change ((((histMap (fun i => (τX i).symm) (fun i => (τY i).symm) k).symm
        ((histMap τX τY k).symm h)), (τX k) ((τX k).symm x)), (τY k) ((τY k).symm y)) = _
      rw [ih]; simp
  funext k
  ext a b
  simp only [relabel, submatrix_apply, h]

/-- **The strategy value is invariant under relabelling.** -/
theorem sdpVal_relabel [∀ i, Nonempty (Y i)] [∀ i, Nonempty (Y' i)]
    (τX : ∀ i, X i ≃ X' i) (τY : ∀ i, Y i ≃ Y' i) {r : ℕ}
    {T : Matrix (Hist X' Y' r) (Hist X' Y' r) ℂ} (hT : T.PosSemidef) :
    sdpVal (T.submatrix (histMap τX τY r) (histMap τX τY r)) = sdpVal T := by
  have hT' : (T.submatrix (histMap τX τY r) (histMap τX τY r)).PosSemidef := hT.submatrix _
  have hpair : ∀ Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ,
      trace (T.submatrix (histMap τX τY r) (histMap τX τY r) * Q r) =
        trace (T * relabel τX τY Q r) := by
    intro Q
    symm
    rw [relabel, ← trace_submatrix_equiv (T * (Q r).submatrix (histMap τX τY r).symm
      (histMap τX τY r).symm) (histMap τX τY r),
      ← submatrix_mul_equiv (e₂ := histMap τX τY r)]
    simp [submatrix_submatrix]
  refine le_antisymm ?_ ?_
  · refine csSup_le (sdpVal_nonempty _) fun _ ⟨Q, hQ, hv⟩ => ?_
    rw [← hv, hpair]
    exact pairing_le_sdpVal hT (isStrategy_relabel τX τY hQ)
  · refine csSup_le (sdpVal_nonempty _) fun _ ⟨Q, hQ, hv⟩ => ?_
    rw [← hv, ← relabel_relabel_symm τX τY Q, ← hpair]
    exact pairing_le_sdpVal hT' (isStrategy_relabel _ _ hQ)

end ShiQIP
