/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Channel

/-!
# Q06 — tensor products, local application and no-signalling

* `reindexMap e` relabels a register; it is a channel.
* `liftR_liftR`: `id_j ⊗ (id_k ⊗ Φ)` is `id_{j × k} ⊗ Φ` up to `regAssoc`. Hence `liftR k Φ`
  (`Φ` on the right register) is CP, TP or a channel whenever `Φ` is.
* `liftL k Φ : MatMap (m × k) (n × k)` applies `Φ` to the **left** register, through `regSwap`.
* `tensorMap Φ Ψ = liftL q Φ ∘ liftR m Ψ` is `Φ ⊗ Ψ`, with `tensorMap_kronecker`:
  `(Φ ⊗ Ψ) (A ⊗ B) = Φ A ⊗ Ψ B`. It is a channel when `Φ` and `Ψ` are.
* **No-signalling** (`traceRight_liftR`): a trace-preserving map applied to the right register
  does not change the marginal of the left register. Conversely, `traceRight_liftL` says the
  partial trace over the untouched right register commutes with `Φ` on the left.

In the protocol semantics the left register is verifier-private memory and the right register
is the prover's message and memory. `traceRight_liftR` is the statement that a prover's channel
cannot change, or reset, the verifier-private marginal.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {j k m n p q : Type}

/-! ## Relabelling registers -/

/-- Relabel a register along `e`. -/
def reindexMap (e : m ≃ n) : MatMap m n := (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap

@[simp] theorem reindexMap_apply (e : m ≃ n) (X : Matrix m m ℂ) :
    reindexMap e X = Matrix.reindex e e X := rfl

theorem liftR_reindexMap (e : m ≃ n) (X : Matrix (k × m) (k × m) ℂ) :
    liftR k (reindexMap e) X =
      Matrix.reindex ((Equiv.refl k).prodCongr e) ((Equiv.refl k).prodCongr e) X := by
  ext P Q; rfl

theorem isChannel_reindexMap [Fintype m] [Fintype n] (e : m ≃ n) : IsChannel (reindexMap e) := by
  refine ⟨fun k _ _ X hX => ?_, fun X => trace_reindex e X⟩
  rw [liftR_reindexMap, reindex_apply]
  exact (posSemidef_submatrix_equiv _).mpr hX

/-! ## Iterated lifting -/

/-- `id_j ⊗ (id_k ⊗ Φ) = id_{j × k} ⊗ Φ`, up to reassociation. -/
theorem liftR_liftR (Φ : MatMap m n) (X : Matrix (j × (k × m)) (j × (k × m)) ℂ) :
    liftR j (liftR k Φ) X =
      Matrix.reindex (regAssoc j k n) (regAssoc j k n)
        (liftR (j × k) Φ (Matrix.reindex (regAssoc j k m).symm (regAssoc j k m).symm X)) := by
  ext ⟨a, c, i⟩ ⟨b, d, l⟩; rfl

theorem IsCP.liftR [Fintype k] [DecidableEq k] [Fintype m] [Fintype n] {Φ : MatMap m n}
    (h : IsCP Φ) : IsCP (ShiQuantum.liftR k Φ) := by
  intro j _ _ X hX
  rw [liftR_liftR]
  simp only [reindex_apply]
  exact (posSemidef_submatrix_equiv _).mpr (h (j × k) _ ((posSemidef_submatrix_equiv _).mpr hX))

theorem IsTP.liftR [Fintype k] [Fintype m] [Fintype n] {Φ : MatMap m n} (h : IsTP Φ) :
    IsTP (ShiQuantum.liftR k Φ) := fun X => by
  simp only [trace, diag_apply, liftR_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := h (blockOf X a a)
  simpa only [trace, diag_apply, blockOf_apply] using this

/-- A channel applied to the right register is a channel on the composite register. -/
theorem IsChannel.liftR [Fintype k] [DecidableEq k] [Fintype m] [Fintype n] {Φ : MatMap m n} (h : IsChannel Φ) :
    IsChannel (ShiQuantum.liftR k Φ) :=
  ⟨h.cp.liftR, h.tp.liftR⟩

/-! ## No-signalling -/

/-- **No-signalling.** A trace-preserving map on the right register leaves the left marginal
unchanged. -/
theorem traceRight_liftR [Fintype m] [Fintype n] {Φ : MatMap m n} (h : IsTP Φ)
    (X : Matrix (k × m) (k × m) ℂ) : traceRight (ShiQuantum.liftR k Φ X) = traceRight X := by
  ext a b
  simp only [traceRight_apply, liftR_apply]
  have := h (blockOf X a b)
  simpa only [trace, diag_apply, blockOf_apply] using this

/-- The left marginal of a state is unchanged by a channel on the right register. -/
theorem IsChannel.marginal_invariant [Fintype m] [Fintype n] {Φ : MatMap m n}
    (h : IsChannel Φ) (ρ : Matrix (k × m) (k × m) ℂ) :
    traceRight (ShiQuantum.liftR k Φ ρ) = traceRight ρ :=
  traceRight_liftR h.tp ρ

/-! ## Acting on the left register -/

/-- `Φ ⊗ id_k`: apply `Φ` to the left register. -/
def liftL (k : Type) (Φ : MatMap m n) : MatMap (m × k) (n × k) :=
  reindexMap (regSwap k n) ∘ₗ liftR k Φ ∘ₗ reindexMap (regSwap m k)

theorem liftL_apply (Φ : MatMap m n) (X : Matrix (m × k) (m × k) ℂ) (i j : n) (c d : k) :
    liftL k Φ X (i, c) (j, d) = Φ (Matrix.of fun i' j' => X (i', c) (j', d)) i j := rfl

theorem IsChannel.liftL [Fintype k] [DecidableEq k] [Fintype m] [Fintype n] {Φ : MatMap m n}
    (h : IsChannel Φ) : IsChannel (ShiQuantum.liftL k Φ) :=
  ((isChannel_reindexMap _).comp h.liftR).comp (isChannel_reindexMap _)

/-- The partial trace over an untouched right register commutes with `Φ` on the left. -/
theorem traceRight_liftL [Fintype k] (Φ : MatMap m n) (X : Matrix (m × k) (m × k) ℂ) :
    traceRight (ShiQuantum.liftL k Φ X) = Φ (traceRight X) := by
  have hX : traceRight X = ∑ c : k, Matrix.of fun i' j' => X (i', c) (j', c) := by
    ext i j; simp [Matrix.sum_apply]
  rw [hX, map_sum]
  ext i j
  simp only [traceRight_apply, liftL_apply, Matrix.sum_apply]

/-! ## Tensor products -/

theorem liftR_kronecker (Φ : MatMap m n) (A : Matrix k k ℂ) (B : Matrix m m ℂ) :
    ShiQuantum.liftR k Φ (A ⊗ₖ B) = A ⊗ₖ Φ B := by
  ext ⟨a, i⟩ ⟨b, l⟩
  have : blockOf (A ⊗ₖ B) a b = A a b • B := by ext; simp
  rw [liftR_apply, this, map_smul]
  simp

theorem liftL_kronecker (Φ : MatMap m n) (B : Matrix m m ℂ) (A : Matrix k k ℂ) :
    ShiQuantum.liftL k Φ (B ⊗ₖ A) = Φ B ⊗ₖ A := by
  ext ⟨i, c⟩ ⟨l, d⟩
  have : (Matrix.of fun i' j' => (B ⊗ₖ A) (i', c) (j', d)) = A c d • B := by
    ext; simp [mul_comm]
  rw [liftL_apply, this, map_smul]
  simp [mul_comm]

/-- `Φ ⊗ Ψ`: first `Ψ` on the right register, then `Φ` on the left register. -/
def tensorMap (Φ : MatMap m n) (Ψ : MatMap p q) : MatMap (m × p) (n × q) :=
  ShiQuantum.liftL q Φ ∘ₗ ShiQuantum.liftR m Ψ

theorem tensorMap_kronecker (Φ : MatMap m n) (Ψ : MatMap p q) (A : Matrix m m ℂ)
    (B : Matrix p p ℂ) : tensorMap Φ Ψ (A ⊗ₖ B) = Φ A ⊗ₖ Ψ B := by
  rw [tensorMap, LinearMap.comp_apply, liftR_kronecker, liftL_kronecker]

theorem IsChannel.tensor [Fintype m] [DecidableEq m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq q] {Φ : MatMap m n}
    {Ψ : MatMap p q} (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) : IsChannel (tensorMap Φ Ψ) :=
  hΦ.liftL.comp hΨ.liftR

/-- Product states go to product states. -/
theorem IsChannel.tensor_product [Fintype m] [DecidableEq m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq q] {Φ : MatMap m n} {Ψ : MatMap p q} (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) {ρ : Matrix m m ℂ}
    {σ : Matrix p p ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    IsDensity (tensorMap Φ Ψ (ρ ⊗ₖ σ)) := by
  rw [tensorMap_kronecker]
  exact (hΦ.map_density hρ).kronecker (hΨ.map_density hσ)

end ShiQuantum
