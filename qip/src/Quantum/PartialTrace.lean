/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Measurement

/-!
# Q05 — partial trace

For the register `α × β` ("`α` then `β`", as in `Quantum.Registers`):

* `traceRight M : Matrix α α' ℂ` traces out `β`: `traceRight M a b = ∑ i, M (a, i) (b, i)`;
* `traceLeft M : Matrix β β' ℂ` traces out `α`: `traceLeft M c d = ∑ a, M (a, c) (a, d)`.

(The kept factor may differ between rows and columns, so partial traces of rectangular
operators such as `(A ⊗ 1) M` are covered.)

Proved here:

* `trace_traceRight`/`trace_traceLeft`: the trace is preserved;
* `traceRight_eq_sum_slice`: `traceRight M = ∑ i, (sliceEmb α i)ᴴ * M * sliceEmb α i`, a
  Kraus-type form from which `posSemidef_traceRight` (PSD is preserved) follows.
  `IsDensity.traceRight` and `IsDensity.traceLeft` combine the two;
* `traceRight_kronecker`: `traceRight (A ⊗ₖ B) = trace B • A`, and the mirror image;
* `traceRight_local`: operations on the kept factor commute with the partial trace;
* locality: `traceRight_mul_one_kronecker_comm` moves an operator on the traced factor around, so
  `traceRight_conj_unitary` shows that a unitary on `β` alone does not change the `α` marginal;
* `trace_mul_traceRight`: duality, `trace (A * traceRight M) = trace ((A ⊗ₖ 1) * M)`;
* register bookkeeping: `traceLeft` is `traceRight` after `regSwap`, tracing a composite register
  is tracing its factors one after another, and tracing a one-dimensional (e.g. zero-qubit)
  register just deletes it.

Examples: the marginal of the Bell state is the maximally mixed qubit (and not pure), and
marginals of product states are their factors.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {α α' β β' γ : Type*}

/-- Trace out the right factor `β` (the kept factor may change from `α` to `α'`). -/
def traceRight [Fintype β] (M : Matrix (α × β) (α' × β) ℂ) : Matrix α α' ℂ :=
  Matrix.of fun a b => ∑ i, M (a, i) (b, i)

/-- Trace out the left factor `α`. -/
def traceLeft [Fintype α] (M : Matrix (α × β) (α × β') ℂ) : Matrix β β' ℂ :=
  Matrix.of fun c d => ∑ a, M (a, c) (a, d)

@[simp] theorem traceRight_apply [Fintype β] (M : Matrix (α × β) (α' × β) ℂ) (a : α) (b : α') :
    traceRight M a b = ∑ i, M (a, i) (b, i) := rfl

@[simp] theorem traceLeft_apply [Fintype α] (M : Matrix (α × β) (α × β') ℂ) (c : β) (d : β') :
    traceLeft M c d = ∑ a, M (a, c) (a, d) := rfl

/-! ## Linearity and trace -/

theorem traceRight_add [Fintype β] (M N : Matrix (α × β) (α' × β) ℂ) :
    traceRight (M + N) = traceRight M + traceRight N := by
  ext a b; simp [Finset.sum_add_distrib]

theorem traceRight_smul [Fintype β] (c : ℂ) (M : Matrix (α × β) (α' × β) ℂ) :
    traceRight (c • M) = c • traceRight M := by
  ext a b; simp [Finset.mul_sum]

theorem traceRight_sub [Fintype β] (M N : Matrix (α × β) (α' × β) ℂ) :
    traceRight (M - N) = traceRight M - traceRight N := by
  ext a b; simp [Finset.sum_sub_distrib]

theorem trace_traceRight [Fintype α] [Fintype β] (M : Matrix (α × β) (α × β) ℂ) :
    trace (traceRight M) = trace M := by
  simp [trace, Fintype.sum_prod_type]

theorem trace_traceLeft [Fintype α] [Fintype β] (M : Matrix (α × β) (α × β) ℂ) :
    trace (traceLeft M) = trace M := by
  simp only [trace, diag_apply, traceLeft_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem traceRight_conjTranspose [Fintype β] (M : Matrix (α × β) (α' × β) ℂ) :
    (traceRight M)ᴴ = traceRight Mᴴ := by
  ext a b; simp [conjTranspose_apply, star_sum]

/-! ## Positivity: a Kraus-type decomposition -/

/-- The embedding `|a⟩ ↦ |a⟩ ⊗ |i⟩`, as a matrix `α × β ← α`. -/
def sliceEmb (α : Type*) [DecidableEq α] [DecidableEq β] (i : β) : Matrix (α × β) α ℂ :=
  Matrix.of fun p b => if p = (b, i) then 1 else 0

theorem traceRight_eq_sum_slice [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) :
    traceRight M = ∑ i : β, (sliceEmb α i)ᴴ * M * sliceEmb α i := by
  ext a b
  simp only [traceRight_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_apply, conjTranspose_apply, sliceEmb, of_apply]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq']

/-- The partial trace of a PSD matrix is PSD. -/
theorem posSemidef_traceRight [Fintype α] [Fintype β] {M : Matrix (α × β) (α × β) ℂ}
    (hM : M.PosSemidef) : (traceRight M).PosSemidef := by
  classical
  rw [traceRight_eq_sum_slice]
  exact posSemidef_sum _ fun i _ => hM.conjTranspose_mul_mul_same (sliceEmb α i)

theorem IsDensity.traceRight [Fintype α] [Fintype β] {M : Matrix (α × β) (α × β) ℂ}
    (h : IsDensity M) : IsDensity (ShiQuantum.traceRight M) :=
  ⟨posSemidef_traceRight h.posSemidef, by rw [trace_traceRight, h.trace_eq_one]⟩

/-! ## Swapping the factors -/

/-- `traceLeft` is `traceRight` after exchanging the factors with `regSwap`. -/
theorem traceLeft_eq_traceRight_swap [Fintype α] (M : Matrix (α × β) (α × β) ℂ) :
    traceLeft M = traceRight (Matrix.reindex (regSwap α β) (regSwap α β) M) := by
  ext c d; simp [regSwap]

theorem posSemidef_traceLeft [Fintype α] [Fintype β] {M : Matrix (α × β) (α × β) ℂ}
    (hM : M.PosSemidef) : (traceLeft M).PosSemidef := by
  rw [traceLeft_eq_traceRight_swap]
  exact posSemidef_traceRight ((posSemidef_submatrix_equiv _).mpr hM)

theorem IsDensity.traceLeft [Fintype α] [Fintype β] {M : Matrix (α × β) (α × β) ℂ}
    (h : IsDensity M) : IsDensity (ShiQuantum.traceLeft M) :=
  ⟨posSemidef_traceLeft h.posSemidef, by rw [trace_traceLeft, h.trace_eq_one]⟩

/-! ## Tensor products -/

theorem traceRight_kronecker [Fintype β] (A : Matrix α α' ℂ) (B : Matrix β β ℂ) :
    traceRight (A ⊗ₖ B) = trace B • A := by
  ext a b
  simp [trace, Finset.mul_sum, mul_comm]

theorem traceLeft_kronecker [Fintype α] (A : Matrix α α ℂ) (B : Matrix β β' ℂ) :
    traceLeft (A ⊗ₖ B) = trace A • B := by
  ext c d
  simp [trace, Finset.sum_mul]

theorem IsDensity.kronecker [Fintype α] [Fintype β] {ρ : Matrix α α ℂ} {σ : Matrix β β ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) : IsDensity (ρ ⊗ₖ σ) :=
  ⟨hρ.posSemidef.kronecker hσ.posSemidef, by
    rw [trace_kronecker, hρ.trace_eq_one, hσ.trace_eq_one, one_mul]⟩

/-- The marginals of a product state are its factors. -/
theorem traceRight_product [Fintype β] {ρ : Matrix α α ℂ} {σ : Matrix β β ℂ}
    (hσ : IsDensity σ) : traceRight (ρ ⊗ₖ σ) = ρ := by
  rw [traceRight_kronecker, hσ.trace_eq_one, one_smul]

theorem traceLeft_product [Fintype α] {ρ : Matrix α α ℂ} {σ : Matrix β β ℂ}
    (hρ : IsDensity ρ) : traceLeft (ρ ⊗ₖ σ) = σ := by
  rw [traceLeft_kronecker, hρ.trace_eq_one, one_smul]

/-! ## Local operations -/

/-- Operations on the kept factor pass through the partial trace (rectangular allowed). -/
theorem traceRight_local {α'' : Type*} [Fintype α] [Fintype α''] [Fintype β] [DecidableEq β]
    (A : Matrix α' α ℂ) (M : Matrix (α × β) (α'' × β) ℂ) (A' : Matrix α'' γ ℂ) :
    traceRight ((A ⊗ₖ (1 : Matrix β β ℂ)) * M * (A' ⊗ₖ (1 : Matrix β β ℂ))) =
      A * traceRight M * A' := by
  ext a b
  simp only [traceRight_apply, mul_apply, kronecker_apply, one_apply, Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

/-- An operator on the traced factor can be moved cyclically. -/
theorem traceRight_mul_one_kronecker_comm [Fintype α] [Fintype β] [DecidableEq α]
    (B : Matrix β β ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    traceRight (((1 : Matrix α α ℂ) ⊗ₖ B) * M) =
      traceRight (M * ((1 : Matrix α α ℂ) ⊗ₖ B)) := by
  ext a b
  simp only [traceRight_apply, mul_apply, kronecker_apply, one_apply, Fintype.sum_prod_type,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  have hL : ∀ x : β, (∑ c : α, ∑ j : β, if a = c then B x j * M (c, j) (b, x) else 0) =
      ∑ j, B x j * M (a, j) (b, x) := fun x => by
    rw [Finset.sum_comm]; simp
  have hR : ∀ x : β, (∑ c : α, ∑ j : β, if c = b then M (a, x) (c, j) * B j x else 0) =
      ∑ j, M (a, x) (b, j) * B j x := fun x => by
    rw [Finset.sum_comm]; simp
  simp only [hL, hR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Locality.** A unitary acting on the traced factor alone leaves the marginal unchanged. -/
theorem traceRight_conj_unitary [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {U : Matrix β β ℂ} (hU : U ∈ Matrix.unitaryGroup β ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    traceRight (((1 : Matrix α α ℂ) ⊗ₖ U) * M * ((1 : Matrix α α ℂ) ⊗ₖ U)ᴴ) =
      traceRight M := by
  rw [Matrix.mul_assoc, traceRight_mul_one_kronecker_comm, conjTranspose_kronecker,
    conjTranspose_one, Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul,
    ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU, one_kronecker_one,
    Matrix.mul_one]

/-- **Duality.** Pairing a marginal with `A` is pairing the state with `A ⊗ 1`. -/
theorem trace_mul_traceRight [Fintype α] [Fintype β] [DecidableEq β] (A : Matrix α α ℂ)
    (M : Matrix (α × β) (α × β) ℂ) :
    trace (A * traceRight M) = trace ((A ⊗ₖ (1 : Matrix β β ℂ)) * M) := by
  simp only [trace, diag_apply, mul_apply, traceRight_apply, kronecker_apply, one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-! ## Register bookkeeping -/

/-- Relabelling the kept factor commutes with the partial trace. -/
theorem traceRight_reindex_left [Fintype β] (e : α ≃ α') (M : Matrix (α × β) (α × β) ℂ) :
    traceRight (Matrix.reindex (e.prodCongr (Equiv.refl β)) (e.prodCongr (Equiv.refl β)) M) =
      Matrix.reindex e e (traceRight M) := by
  ext a b; simp

/-- Relabelling the traced factor does not change the partial trace. -/
theorem traceRight_reindex_right [Fintype β] [Fintype β'] (f : β ≃ β')
    (M : Matrix (α × β) (α × β) ℂ) :
    traceRight (Matrix.reindex ((Equiv.refl α).prodCongr f) ((Equiv.refl α).prodCongr f) M) =
      traceRight M := by
  ext a b
  simp only [traceRight_apply, reindex_apply, submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm, Equiv.refl_apply]
  exact Equiv.sum_comp f.symm (fun i => M (a, i) (b, i))

/-- Tracing out `β × γ` is tracing out `γ`, then `β`. -/
theorem traceRight_prod [Fintype β] [Fintype γ] (M : Matrix (α × (β × γ)) (α × (β × γ)) ℂ) :
    traceRight M =
      traceRight (traceRight (Matrix.reindex (regAssoc α β γ).symm (regAssoc α β γ).symm M)) := by
  ext a b
  simp [regAssoc, Fintype.sum_prod_type]

/-- Tracing out a one-dimensional register (for instance zero qubits) just deletes it. -/
theorem traceRight_unique [Fintype β] [Unique β] (M : Matrix (α × β) (α × β) ℂ) (a b : α) :
    traceRight M a b = M (a, default) (b, default) := by
  simp

theorem traceRight_unitRight (M : Matrix (α × Unit) (α × Unit) ℂ) :
    traceRight M = Matrix.reindex (regUnitRight α) (regUnitRight α) M := by
  ext a b; simp [regUnitRight]

/-! ## Examples -/

/-- The amplitude `1/√2`. -/
noncomputable def invSqrtTwo : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

theorem invSqrtTwo_mul_star : invSqrtTwo * (starRingEnd ℂ) invSqrtTwo = 1 / 2 := by
  rw [invSqrtTwo, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

/-- The Bell vector `(|00⟩ + |11⟩) / √2`. -/
noncomputable def bellVec : Bool × Bool → ℂ := fun p => if p.1 = p.2 then invSqrtTwo else 0

/-- The marginal of the Bell state is the maximally mixed qubit. -/
theorem traceRight_bell : traceRight (pureState bellVec) = maxMixed Bool := by
  ext a b
  simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply, bellVec,
    Fintype.sum_bool, maxMixed, Matrix.smul_apply, Fintype.card_bool]
  cases a <;> cases b <;> simp [invSqrtTwo_mul_star]

theorem isDensity_bell : IsDensity (pureState bellVec) := by
  refine ⟨pureState_posSemidef _, ?_⟩
  simp only [pureState, trace, diag_apply, vecMulVec_apply, Pi.star_apply, bellVec,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp [invSqrtTwo_mul_star]
  norm_num

/-- The Bell marginal is mixed although the Bell state is pure: it is not a pure state. -/
theorem traceRight_bell_not_pure :
    ¬ ∃ v : Bool → ℂ, pureState v = traceRight (pureState bellVec) := by
  rintro ⟨v, hv⟩
  rw [traceRight_bell] at hv
  have h00 := congrFun (congrFun hv false) false
  have h11 := congrFun (congrFun hv true) true
  have h01 := congrFun (congrFun hv false) true
  simp [pureState, vecMulVec_apply, maxMixed, one_apply] at h00 h11 h01
  rcases h01 with h | h
  · simp [h] at h00
  · simp [h] at h11

end ShiQuantum
