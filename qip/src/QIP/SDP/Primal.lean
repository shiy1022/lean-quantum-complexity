/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Value

/-!
# Q22 — the primal strategy SDP

The variables of the strategy SDP for `r` turns form the finite family
`Q : ∀ k : Fin (r+1), Matrix (Hist k) (Hist k) ℂ`. The causal constraints are the kernel of a
**real-linear map**

  `causalMap r Q k = Tr_{Y_k} Q_{k+1} − Q_k ⊗ 1_{X_k}`   (`k : Fin r`)

with values in `∀ k : Fin r, Matrix (Hist k × X k) (Hist k × X k) ℂ`. Both spaces are
finite-dimensional real vector spaces. `causalMap` maps Hermitian families to Hermitian families
(`causalMap_isHermitian`).

**Adjoints.** The real trace pairing is `⟪A, B⟫ = Re tr (A B)`; on Hermitian matrices this is the
Hilbert–Schmidt inner product. The two pieces of each constraint have the explicit adjoints

* `Q' ↦ Tr_{Y} Q'`, adjoint `W ↦ W ⊗ 1_Y` (`trace_mul_traceRight`);
* `Q ↦ Q ⊗ 1_X`, adjoint `W ↦ Tr_X W` (`trace_mul_kron_one`).

Hence the Lagrangian identity `pairing_causalMap`:

  `Σ_k ⟪W_k, causalMap Q k⟫ = Σ_k ⟪W_k ⊗ 1, Q_{k+1}⟫ − Σ_k ⟪Tr_X W_k, Q_k⟫`.

The dual program of `QIP.SDP.WeakDuality` is read off from this identity.

* `isStrategy_iff_causalMap`: `IsStrategy r Q` is exactly `Q_0 = 1`, `Q_k ⪰ 0` and
  `causalMap r Q = 0`.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## The two adjoint identities -/

/-- Adjoint of `Q' ↦ Tr Q'`: `tr ((A ⊗ 1) M) = tr (A · Tr M)`. -/
theorem trace_kron_one_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    trace ((A ⊗ₖ (1 : Matrix β β ℂ)) * M) = trace (A * traceRight M) :=
  (trace_mul_traceRight A M).symm

/-- Adjoint of `Q ↦ Q ⊗ 1`: `tr (W (Q ⊗ 1)) = tr (Tr W · Q)`. -/
theorem trace_mul_kron_one {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (W : Matrix (α × β) (α × β) ℂ) (Q : Matrix α α ℂ) :
    trace (W * (Q ⊗ₖ (1 : Matrix β β ℂ))) = trace (traceRight W * Q) := by
  rw [trace_mul_comm, trace_kron_one_mul, trace_mul_comm]

/-- One link of the telescope: `tr ((W ⊗ 1) Q') = tr (Tr W · Q)` when `Tr Q' = Q ⊗ 1`. -/
theorem trace_causal_link {H A B : Type} [Fintype H] [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (W : Matrix (H × A) (H × A) ℂ) (Q' : Matrix ((H × A) × B) ((H × A) × B) ℂ)
    (Q : Matrix H H ℂ) (hc : traceRight Q' = Q ⊗ₖ (1 : Matrix A A ℂ)) :
    trace ((W ⊗ₖ (1 : Matrix B B ℂ)) * Q') = trace (traceRight W * Q) := by
  rw [trace_kron_one_mul, hc, trace_mul_kron_one]

/-! ## The constraint map -/

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

variable (X Y) in
/-- Primal variables: one matrix per prefix length `k ≤ r`. -/
abbrev PrimalVar (r : ℕ) := ∀ k : Fin (r + 1), Matrix (Hist X Y k) (Hist X Y k) ℂ

variable (X Y) in
/-- Constraint values (equivalently, dual multipliers): one matrix on `Hist k × X k` per `k < r`. -/
abbrev ConstrVar (r : ℕ) := ∀ k : Fin r, Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ

/-- `Q_{k+1}` viewed on `(Hist k × X k) × Y k`. -/
def succView {r : ℕ} (Q : PrimalVar X Y r) (k : Fin r) :
    Matrix ((Hist X Y k × X k) × Y k) ((Hist X Y k × X k) × Y k) ℂ :=
  Q k.succ

/-- `Q_k` viewed on `Hist k`. -/
def castView {r : ℕ} (Q : PrimalVar X Y r) (k : Fin r) : Matrix (Hist X Y k) (Hist X Y k) ℂ :=
  Q k.castSucc

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem succView_add {r : ℕ} (Q Q' : PrimalVar X Y r) (k : Fin r) :
    succView (Q + Q') k = succView Q k + succView Q' k := rfl

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem castView_add {r : ℕ} (Q Q' : PrimalVar X Y r) (k : Fin r) :
    castView (Q + Q') k = castView Q k + castView Q' k := rfl

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem succView_smul {r : ℕ} (c : ℝ) (Q : PrimalVar X Y r) (k : Fin r) :
    succView (c • Q) k = c • succView Q k := rfl

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem castView_smul {r : ℕ} (c : ℝ) (Q : PrimalVar X Y r) (k : Fin r) :
    castView (c • Q) k = c • castView Q k := rfl

/-- The `k`-th causal residual `Tr_{Y_k} Q_{k+1} − Q_k ⊗ 1_{X_k}`. -/
noncomputable def causalRes {r : ℕ} (Q : PrimalVar X Y r) (k : Fin r) :
    Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ :=
  traceRight (succView Q k) -
    castView Q k ⊗ₖ (1 : Matrix (X k) (X k) ℂ)

variable (X Y) in
/-- **The causal constraint map**, real-linear between finite-dimensional real spaces. -/
noncomputable def causalMap (r : ℕ) : PrimalVar X Y r →ₗ[ℝ] ConstrVar X Y r where
  toFun Q k := causalRes Q k
  map_add' Q Q' := by
    funext k
    simp only [causalRes, succView_add, castView_add, traceRight_add, add_kronecker, Pi.add_apply]
    abel
  map_smul' c Q := by
    funext k
    simp only [causalRes, succView_smul, castView_smul, RingHom.id_apply, Pi.smul_apply]
    rw [← algebraMap_smul ℂ c (succView Q k), ← algebraMap_smul ℂ c (castView Q k),
      traceRight_smul, smul_kronecker, ← smul_sub, algebraMap_smul]

omit [∀ i, Fintype (X i)] [∀ i, DecidableEq (Y i)] in
theorem causalMap_apply {r : ℕ} (Q : PrimalVar X Y r) (k : Fin r) :
    causalMap X Y r Q k = causalRes Q k := rfl

omit [∀ i, Fintype (X i)] [∀ i, DecidableEq (Y i)] in
/-- `causalMap` preserves Hermitian families. -/
theorem causalMap_isHermitian {r : ℕ} {Q : PrimalVar X Y r} (hQ : ∀ k, (Q k).IsHermitian)
    (k : Fin r) : (causalMap X Y r Q k).IsHermitian := by
  rw [causalMap_apply, causalRes]
  refine IsHermitian.sub ?_ ?_
  · have h : (succView Q k)ᴴ = succView Q k := hQ k.succ
    unfold IsHermitian
    rw [traceRight_conjTranspose, h]
  · have h : (castView Q k)ᴴ = castView Q k := hQ k.castSucc
    unfold IsHermitian
    rw [conjTranspose_kronecker, conjTranspose_one, h]

/-- The restriction of an `ℕ`-indexed family to a primal variable. -/
def toPrimal (r : ℕ) (Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ) : PrimalVar X Y r :=
  fun k => Q k

omit [∀ i, Fintype (X i)] in
/-- **The strategy constraints in SDP form.** -/
theorem isStrategy_iff_causalMap {r : ℕ} {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} :
    IsStrategy r Q ↔
      Q 0 = 1 ∧ (∀ k ≤ r, (Q k).PosSemidef) ∧ causalMap X Y r (toPrimal r Q) = 0 := by
  constructor
  · intro h
    refine ⟨h.zero, h.posSemidef, ?_⟩
    funext k
    rw [causalMap_apply, causalRes, Pi.zero_apply, sub_eq_zero]
    exact h.causal k k.isLt
  · rintro ⟨h0, hp, hc⟩
    refine ⟨h0, hp, fun k hk => ?_⟩
    have := congrFun hc ⟨k, hk⟩
    rw [causalMap_apply, causalRes, Pi.zero_apply, sub_eq_zero] at this
    exact this

/-! ## The Lagrangian identity -/

/-- **The adjoint of `causalMap`, componentwise.** -/
theorem trace_mul_causalRes {r : ℕ} (Q : PrimalVar X Y r) (W : ConstrVar X Y r) (k : Fin r) :
    trace (W k * causalRes Q k) =
      trace ((W k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ)) *
          succView Q k) -
        trace (traceRight (W k) * castView Q k) := by
  rw [causalRes, Matrix.mul_sub, trace_sub, trace_mul_traceRight, trace_mul_kron_one]

/-- **The Lagrangian identity** for the real trace pairing. -/
theorem pairing_causalMap {r : ℕ} (Q : PrimalVar X Y r) (W : ConstrVar X Y r) :
    ∑ k, (trace (W k * causalMap X Y r Q k)).re =
      ∑ k : Fin r, (trace ((W k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ)) *
          succView Q k)).re -
        ∑ k : Fin r, (trace (traceRight (W k) *
          castView Q k)).re := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [causalMap_apply, trace_mul_causalRes, Complex.sub_re]

end ShiQIP
