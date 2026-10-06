/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.SDP.Primal

/-!
# Q22 — the tailored strategy SDP and weak duality

**Primal.** Maximize `Re tr (T Q_r)` over causal strategy families `IsStrategy r Q`
(`QIP.StrategyOperator`): `Q_0 = 1`, `Q_k ⪰ 0`, `Tr_{Y_k} Q_{k+1} = Q_k ⊗ 1_{X_k}`.

**Dual (derived from these constraints).** A certificate `DualCert T r t` consists of matrices
`Z_k` on `Hist_k` (`k ≤ r`) and `W_k` on `Hist_k × X_k` (`k < r`) with

* `T ≤ Z_r`,
* `Z_{k+1} ≤ W_k ⊗ 1_{Y_k}`,
* `Tr_{X_k} W_k ≤ Z_k`,
* `Z_0 ≤ t · 1`.

The multiplier `W_k` is the adjoint variable of the `k`-th causal equation. The adjoint of
`Q ↦ Tr_{Y_k} Q` is `W ↦ W ⊗ 1_{Y_k}`, and the adjoint of `Q ↦ Q ⊗ 1_{X_k}` is
`W ↦ Tr_{X_k} W` (`QIP.SDP.Primal`: `trace_mul_traceRight`, `trace_mul_kron_one`, `pairing_causalMap`).

* **`DualCert.weak_duality`**: every certificate bounds every causal strategy,
  `Re tr (T Q_r) ≤ t`. The proof telescopes `Re tr (Z_k Q_k)` down the causal chain, using only
  the PSD order and the two adjoint identities.
* **`DualCert.accept_le`**: through Q20, a certificate for `tester d` bounds the acceptance
  probability of every operational prover.
* **`psd_le_trace_smul_one`**: `M ⪰ 0 ⇒ M ≤ (tr M) · 1`. With it, `scalarCert` is an explicit
  certificate for any PSD `T`, with `t = Re tr T · ∏ |X_k|`; `accept_le_trace_tester` is the
  resulting concrete bound.

No numerical solver is involved; certificates are exact matrices.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker InnerProductSpace

/-! ## Dual certificates -/

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

/-- A dual certificate with objective `t` for `max Re tr (T Q_r)`. -/
structure DualCert (r : ℕ) (T : Matrix (Hist X Y r) (Hist X Y r) ℂ) (t : ℝ) where
  Z : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ
  W : ∀ k, Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ
  top : T ≤ Z r
  step_out : ∀ k < r, (Z (k + 1) : Matrix ((Hist X Y k × X k) × Y k) ((Hist X Y k × X k) × Y k) ℂ)
    ≤ W k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ)
  step_in : ∀ k < r, traceRight (W k) ≤ Z k
  bottom : Z 0 ≤ ((t : ℂ) • (1 : Matrix (Hist X Y 0) (Hist X Y 0) ℂ))

theorem re_trace_mul_mono {n : Type} [Fintype n] [DecidableEq n] {A B P : Matrix n n ℂ}
    (h : A ≤ B) (hP : P.PosSemidef) : (trace (A * P)).re ≤ (trace (B * P)).re :=
  (Complex.le_def.mp (trace_mul_mono h hP)).1

/-- **Weak duality**: a certificate bounds every causal strategy. -/
theorem DualCert.weak_duality {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ} {t : ℝ}
    (C : DualCert r T t) {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (hQ : IsStrategy r Q) :
    (trace (T * Q r)).re ≤ t := by
  have key : ∀ k ≤ r, (trace (C.Z k * Q k)).re ≤ t := by
    intro k hk
    induction k with
    | zero =>
      have h0 := re_trace_mul_mono C.bottom (hQ.posSemidef 0 (Nat.zero_le _))
      rw [hQ.zero, Matrix.mul_one, Matrix.mul_one, trace_smul, trace_one] at h0
      rw [hQ.zero, Matrix.mul_one]
      have hc : Fintype.card (Hist X Y 0) = 1 := Fintype.card_unit
      rw [hc] at h0
      simpa using h0
    | succ k ih =>
      have hk' : k < r := by omega
      have h1 := re_trace_mul_mono (C.step_out k hk') (hQ.posSemidef (k + 1) hk)
      -- tr ((W ⊗ 1) Q_{k+1}) = tr (W · Tr_Y Q_{k+1}) = tr (W (Q_k ⊗ 1)) = tr (Tr_X W · Q_k)
      have e1 := congrArg Complex.re (trace_causal_link (C.W k) _ _ (hQ.causal k hk'))
      have h2 := re_trace_mul_mono (C.step_in k hk') (hQ.posSemidef k (by omega))
      exact (h1.trans (le_of_eq e1)).trans (h2.trans (ih (by omega)))
  have h := re_trace_mul_mono C.top (hQ.posSemidef r le_rfl)
  linarith [key r le_rfl]

/-- **A certificate for the tester bounds every operational prover.** -/
theorem DualCert.accept_le {d : Desc} {t : ℝ} (C : DualCert d.numMsgs (tester d) t)
    (P : Prover d) : accept P ≤ t := by
  rw [accept_eq_pairing]
  exact C.weak_duality (opStrategy_isStrategy P)

theorem DualCert.value_le {d : Desc} {t : ℝ} (C : DualCert d.numMsgs (tester d) t) :
    value d ≤ t :=
  (value_le_iff d t).mp fun P => C.accept_le P

/-! ## A concrete certificate -/

/-- `x* (B Bᴴ) x ≤ tr (B Bᴴ) · |x|²` (Cauchy–Schwarz column by column). -/
theorem quad_le_trace_mul {n r : Type} [Fintype n] [Fintype r] (B : Matrix n r ℂ) (x : n → ℂ) :
    ‖toE (Bᴴ *ᵥ x)‖ ^ 2 ≤ (trace (B * Bᴴ)).re * ‖toE x‖ ^ 2 := by
  have hcol : ∀ k, ‖(Bᴴ *ᵥ x) k‖ ≤ ‖toE (fun i => B i k)‖ * ‖toE x‖ := by
    intro k
    have : (Bᴴ *ᵥ x) k = ⟪toE (fun i => B i k), toE x⟫_ℂ := by
      rw [inner_toE]; simp [mulVec, dotProduct, conjTranspose_apply]
    rw [this]; exact norm_inner_le_norm _ _
  rw [norm_toE_sq]
  calc ∑ k, ‖(Bᴴ *ᵥ x) k‖ ^ 2 ≤ ∑ k, (‖toE (fun i => B i k)‖ * ‖toE x‖) ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hcol k) 2
    _ = (∑ k, ‖toE (fun i => B i k)‖ ^ 2) * ‖toE x‖ ^ 2 := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = (trace (B * Bᴴ)).re * ‖toE x‖ ^ 2 := by
        congr 1
        simp only [norm_toE_sq, trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **A PSD matrix is at most its trace times the identity.** -/
theorem psd_le_trace_smul_one {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : M ≤ (((trace M).re : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
  obtain ⟨B, rfl⟩ := PSD_exists_eq_mul_conjTranspose hM
  rw [Matrix.le_iff]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (posSemidef_self_mul_conjTranspose B).isHermitian
    simp [IsHermitian, conjTranspose_smul]
  · rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      ← mulVec_mulVec, dotProduct_mulVec]
    have h3 : star x ᵥ* B = star (Bᴴ *ᵥ x) := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [h3]
    have h1 := norm_toE_sq_eq_dotProduct x
    have h2 := norm_toE_sq_eq_dotProduct (Bᴴ *ᵥ x)
    rw [← h1, ← h2, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.zero_le_real]
    linarith [quad_le_trace_mul B x]

/-- The scalar weights `c_k = Re tr T · ∏_{k ≤ i < r} |X_i|`. -/
noncomputable def scalarWeight (X : ℕ → Type) [∀ i, Fintype (X i)] (r : ℕ) (τ : ℝ) (k : ℕ) : ℝ :=
  τ * ∏ i ∈ Finset.Ico k r, (Fintype.card (X i) : ℝ)

theorem scalarWeight_succ (X : ℕ → Type) [∀ i, Fintype (X i)] {r k : ℕ} (τ : ℝ) (hk : k < r) :
    scalarWeight X r τ k = scalarWeight X r τ (k + 1) * Fintype.card (X k) := by
  unfold scalarWeight
  rw [Finset.prod_eq_prod_Ico_succ_bot hk]
  ring

theorem kron_smul_one {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β] (c : ℂ) :
    (c • (1 : Matrix α α ℂ)) ⊗ₖ (1 : Matrix β β ℂ) = c • (1 : Matrix (α × β) (α × β) ℂ) := by
  rw [smul_kronecker, one_kronecker_one]

theorem traceRight_smul_one {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β] (c : ℂ) :
    traceRight (c • (1 : Matrix (α × β) (α × β) ℂ)) =
      (c * Fintype.card β) • (1 : Matrix α α ℂ) := by
  rw [← one_kronecker_one, ← smul_kronecker, traceRight_kronecker, trace_one, smul_smul,
    mul_comm]

/-- **The scalar certificate** for a PSD objective `T`: `Z_k = c_k · 1`, `W_k = c_{k+1} · 1`. -/
noncomputable def scalarCert {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ}
    (hT : T.PosSemidef) : DualCert r T (scalarWeight X r (trace T).re 0) where
  Z k := ((scalarWeight X r (trace T).re k : ℝ) : ℂ) • 1
  W k := ((scalarWeight X r (trace T).re (k + 1) : ℝ) : ℂ) • 1
  top := by
    have h := psd_le_trace_smul_one hT
    unfold scalarWeight
    simpa using h
  step_out k _ := le_of_eq (kron_smul_one _).symm
  step_in k hk := le_of_eq (by
    rw [traceRight_smul_one, scalarWeight_succ X _ hk]; push_cast; rfl)
  bottom := le_rfl

/-- **Explicit bound**: every causal strategy has `Re tr (T Q_r) ≤ Re tr T · ∏_{i<r} |X_i|`. -/
theorem pairing_le_trace_mul_card {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ}
    (hT : T.PosSemidef) {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (hQ : IsStrategy r Q) :
    (trace (T * Q r)).re ≤ (trace T).re * ∏ i ∈ Finset.range r, (Fintype.card (X i) : ℝ) := by
  have := (scalarCert hT).weak_duality hQ
  rwa [scalarWeight, ← Finset.range_eq_Ico] at this

/-- **The concrete bound through Q20**: every operational prover accepts with probability at most
`Re tr (tester d) · ∏_{j<m} 2^{|message j|}`. -/
theorem accept_le_trace_tester {d : Desc} (P : Prover d) :
    accept P ≤ (trace (tester d)).re *
      ∏ i ∈ Finset.range d.numMsgs, (Fintype.card (Reg d i) : ℝ) := by
  have := (scalarCert (tester_posSemidef d)).accept_le P
  rwa [scalarWeight, ← Finset.range_eq_Ico] at this

end ShiQIP
