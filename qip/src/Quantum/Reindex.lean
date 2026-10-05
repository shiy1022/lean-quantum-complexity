/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Registers

/-!
# Q02 — reindexing matrices and state maps

For a basis equivalence `e : α ≃ β`, `permMat e : Matrix β α ℂ` is the permutation matrix
`|a⟩ ↦ |e a⟩`, and `reindexState e` is its action on coordinate vectors. We prove the inverse,
adjoint and composition laws, that conjugation by `permMat e` is `Matrix.reindex e e`, and the
Kronecker-product identities for the named register equivalences of `Quantum.Registers`
(associativity, swap, swap twice, and adding/removing a trivial register).
-/

namespace ShiQuantum

open Matrix
open scoped Kronecker

variable {α β γ : Type*}

/-! ## State maps -/

/-- Relabel a coordinate vector along `e`: `(reindexState e v) (e a) = v a`. -/
def reindexState (e : α ≃ β) (v : α → ℂ) : β → ℂ := fun b => v (e.symm b)

@[simp] theorem reindexState_apply (e : α ≃ β) (v : α → ℂ) (b : β) :
    reindexState e v b = v (e.symm b) := rfl

@[simp] theorem reindexState_refl (v : α → ℂ) : reindexState (Equiv.refl α) v = v := rfl

theorem reindexState_trans (e : α ≃ β) (f : β ≃ γ) (v : α → ℂ) :
    reindexState (e.trans f) v = reindexState f (reindexState e v) := rfl

@[simp] theorem reindexState_symm_self (e : α ≃ β) (v : α → ℂ) :
    reindexState e.symm (reindexState e v) = v := by
  funext a; simp

@[simp] theorem reindexState_self_symm (e : α ≃ β) (w : β → ℂ) :
    reindexState e (reindexState e.symm w) = w := by
  funext b; simp

/-- Relabelling preserves the Euclidean inner product. -/
theorem reindexState_inner [Fintype α] [Fintype β] (e : α ≃ β) (v w : α → ℂ) :
    ∑ b, star (reindexState e v b) * reindexState e w b = ∑ a, star (v a) * w a :=
  Equiv.sum_comp e.symm (fun a => star (v a) * w a)

/-! ## Permutation matrices -/

/-- The permutation matrix `|a⟩ ↦ |e a⟩`. -/
def permMat [DecidableEq β] (e : α ≃ β) : Matrix β α ℂ :=
  Matrix.of fun b a => if e a = b then 1 else 0

theorem permMat_apply [DecidableEq β] (e : α ≃ β) (b : β) (a : α) :
    permMat e b a = if e a = b then 1 else 0 := rfl

theorem permMat_apply' [DecidableEq α] [DecidableEq β] (e : α ≃ β) (b : β) (a : α) :
    permMat e b a = if a = e.symm b then 1 else 0 := by
  rw [permMat_apply]
  congr 1
  exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩

theorem permMat_mulVec [Fintype α] [DecidableEq α] [DecidableEq β] (e : α ≃ β) (v : α → ℂ) :
    permMat e *ᵥ v = reindexState e v := by
  funext b
  simp [mulVec, dotProduct, permMat_apply']

theorem permMat_refl [DecidableEq α] : permMat (Equiv.refl α) = 1 := by
  ext a b
  simp [permMat_apply, Matrix.one_apply, eq_comm]

theorem permMat_trans [Fintype β] [DecidableEq β] [DecidableEq γ] (e : α ≃ β) (f : β ≃ γ) :
    permMat (e.trans f) = permMat f * permMat e := by
  ext c a
  rw [mul_apply, Finset.sum_eq_single (e a)]
  · simp [permMat_apply]; rfl
  · intro b _ hb
    simp [permMat_apply, Ne.symm hb]
  · simp

theorem permMat_conjTranspose [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    (permMat e)ᴴ = permMat e.symm := by
  ext a b
  simp only [conjTranspose_apply, permMat_apply, Equiv.symm_apply_eq]
  by_cases h : e a = b
  · simp [h]
  · have h' : ¬ b = e a := fun h'' => h h''.symm
    simp [h, h']

theorem permMat_mul_symm [Fintype α] [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    permMat e * permMat e.symm = 1 := by
  rw [← permMat_trans, Equiv.symm_trans_self, permMat_refl]

theorem permMat_symm_mul [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    permMat e.symm * permMat e = 1 := by
  rw [← permMat_trans, Equiv.self_trans_symm, permMat_refl]

/-- A permutation matrix is unitary: `Pᴴ P = 1` and `P Pᴴ = 1`. -/
theorem permMat_conjTranspose_mul [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    (permMat e)ᴴ * permMat e = 1 := by
  rw [permMat_conjTranspose, permMat_symm_mul]

theorem permMat_mul_conjTranspose [Fintype α] [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    permMat e * (permMat e)ᴴ = 1 := by
  rw [permMat_conjTranspose, permMat_mul_symm]

/-- Conjugation by a permutation matrix is `Matrix.reindex`. -/
theorem permMat_conj [Fintype α] [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (M : Matrix α α ℂ) : permMat e * M * (permMat e)ᴴ = Matrix.reindex e e M := by
  ext b b'
  rw [permMat_conjTranspose]
  simp only [mul_apply, permMat_apply', reindex_apply, submatrix_apply, ite_mul, one_mul,
    zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.symm_symm]
  rw [Finset.sum_eq_single (e.symm b')]
  · simp
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (by rw [h]; simp)
  · simp

/-! ## Tensor products of states -/

/-- The product state `v ⊗ w` on `α × β`, with `α` the left factor. -/
def tensorState (v : α → ℂ) (w : β → ℂ) : α × β → ℂ := fun p => v p.1 * w p.2

theorem tensorState_assoc (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    reindexState (regAssoc α β γ) (tensorState (tensorState u v) w) =
      tensorState u (tensorState v w) := by
  funext ⟨a, b, c⟩
  simp [tensorState, regAssoc, mul_assoc]

theorem tensorState_swap (v : α → ℂ) (w : β → ℂ) :
    reindexState (regSwap α β) (tensorState v w) = tensorState w v := by
  funext ⟨b, a⟩
  simp [tensorState, regSwap, mul_comm]

/-- Tensoring with the one-dimensional state `1` and removing the trivial register is exact. -/
theorem tensorState_unitRight (v : α → ℂ) :
    reindexState (regUnitRight α) (tensorState v (fun _ : Unit => 1)) = v := by
  funext a
  simp [tensorState, regUnitRight]

/-! ## Kronecker identities for the named equivalences -/

variable {α' β' γ' : Type*}

/-- Associativity of the tensor product, as an exact reindexing identity. -/
theorem kron_regAssoc (A : Matrix α α' ℂ) (B : Matrix β β' ℂ) (C : Matrix γ γ' ℂ) :
    Matrix.reindex (regAssoc α β γ) (regAssoc α' β' γ') (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) :=
  Matrix.kronecker_assoc A B C

/-- Swapping the factors of a Kronecker product. -/
theorem kron_regSwap (A : Matrix α α' ℂ) (B : Matrix β β' ℂ) :
    Matrix.reindex (regSwap α β) (regSwap α' β') (A ⊗ₖ B) = B ⊗ₖ A := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [regSwap, mul_comm]

/-- Swapping twice is the identity on every matrix over a product register. -/
theorem reindex_regSwap_twice (M : Matrix (α × β) (α' × β') ℂ) :
    Matrix.reindex (regSwap β α) (regSwap β' α')
      (Matrix.reindex (regSwap α β) (regSwap α' β') M) = M := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  rfl

/-- Tensoring with the `1 × 1` identity and removing the trivial register is exact. -/
theorem kron_regUnitRight (A : Matrix α α' ℂ) :
    Matrix.reindex (regUnitRight α) (regUnitRight α') (A ⊗ₖ (1 : Matrix Unit Unit ℂ)) = A := by
  ext a a'
  simp [regUnitRight]

/-- Kronecker products of permutation matrices are permutation matrices of the product map. -/
theorem permMat_prodCongr [Fintype α] [Fintype β] [DecidableEq α'] [DecidableEq β']
    (e : α ≃ α') (f : β ≃ β') :
    permMat (e.prodCongr f) = permMat e ⊗ₖ permMat f := by
  ext ⟨a', b'⟩ ⟨a, b⟩
  simp only [permMat_apply, kronecker_apply, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  split_ifs <;> simp_all

end ShiQuantum
