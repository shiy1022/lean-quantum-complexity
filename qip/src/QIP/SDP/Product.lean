/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.SDP.StrongDuality

/-!
# Q24 — the product bound against entangled strategies

Two strategy games `(X₁, Y₁, T₁)` and `(X₂, Y₂, T₂)` with `r` turns are played **in parallel**
with joint messages `X₁ i × X₂ i` and `Y₁ i × Y₂ i`, and accepted iff both accept. The joint
tester is `prodMat T₁ T₂ = (T₁ ⊗ T₂)` reindexed along `histEquiv`, the canonical
identification of joint histories with pairs of histories.

The strategy value of a tester is `sdpVal T = sup {Re tr (T Q_r) : IsStrategy r Q}`.

* **`sdpVal_prod`**: `sdpVal (prodMat T₁ T₂) = sdpVal T₁ * sdpVal T₂` for PSD testers.
  * *Upper bound* — the supremum is over **all** joint causal strategies, entangled ones
    included. Approximate certificates of Q23 are tensored (`DualCert.prod`): every inequality
    is multiplied in the PSD order (`kron_le_kron`, using that certificates for PSD testers are
    PSD, `DualCert.posSemidef_Z`). Weak duality bounds every joint strategy by
    `(V₁ + η)(V₂ + η)`; then `η → 0`.
  * *Lower bound* — products of strategies are strategies (`isStrategy_prod`), and the pairing
    factorizes.
* **`value_eq_sdpVal`**: the game value of a verifier is the strategy value of its tester.

The operational parallel-repetition verifier, and the identification of its tester with
`prodMat`, is Q25.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Order facts for Kronecker products -/

theorem kron_le_kron {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A B : Matrix m m ℂ} {C D : Matrix n n ℂ} (hAB : A ≤ B) (hCD : C ≤ D) (hA : A.PosSemidef)
    (hD : D.PosSemidef) : A ⊗ₖ C ≤ B ⊗ₖ D := by
  rw [Matrix.le_iff] at hAB hCD ⊢
  have e : B ⊗ₖ D - A ⊗ₖ C = (B - A) ⊗ₖ D + A ⊗ₖ (D - C) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, kroneckerMap_apply]
    ring
  rw [e]
  exact (hAB.kronecker hD).add (hA.kronecker hCD)

theorem submatrix_le_submatrix {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A B : Matrix n n ℂ} (h : A ≤ B) (e : m ≃ n) :
    A.submatrix e e ≤ B.submatrix e e := by
  rw [Matrix.le_iff] at h ⊢
  exact h.submatrix e

theorem trace_submatrix_equiv {m n : Type} [Fintype m] [Fintype n] (A : Matrix n n ℂ)
    (e : m ≃ n) : trace (A.submatrix e e) = trace A := by
  simp only [trace, diag_apply, submatrix_apply]
  exact e.sum_comp (fun i => A i i)

theorem psd_of_kron_one {n β : Type} [Fintype n] [Fintype β] [DecidableEq n] [DecidableEq β]
    [Nonempty β] {W : Matrix n n ℂ}
    (h : (W ⊗ₖ (1 : Matrix β β ℂ)).PosSemidef) : W.PosSemidef := by
  have h2 := posSemidef_traceRight h
  rw [traceRight_kronecker, trace_one] at h2
  have hc : (0 : ℂ) < (Fintype.card β : ℂ) := by exact_mod_cast Fintype.card_pos
  have : W = ((Fintype.card β : ℂ)⁻¹) • ((Fintype.card β : ℂ) • W) := by
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [this]
  exact h2.smul (inv_nonneg.mpr hc.le)

/-! ## Certificates for PSD testers are PSD -/

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

theorem posSemidef_of_ge {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (h : A ≤ B) : B.PosSemidef := by
  rw [Matrix.le_iff] at h
  have := hA.add h
  rwa [add_sub_cancel] at this

/-- In a certificate for a PSD tester, every `Z_k` (`k ≤ r`) and `W_k` (`k < r`) is PSD. -/
theorem DualCert.posSemidef_Z [∀ i, Nonempty (Y i)] {r : ℕ}
    {T : Matrix (Hist X Y r) (Hist X Y r) ℂ} {t : ℝ} (C : DualCert r T t)
    (hT : T.PosSemidef) : ∀ n ≤ r, (C.Z (r - n)).PosSemidef ∧
      (n ≠ 0 → (C.W (r - n)).PosSemidef) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨posSemidef_of_ge hT C.top, fun h => absurd rfl h⟩
  | succ n ih =>
    intro hn
    obtain ⟨hZ, -⟩ := ih (by omega)
    have hk : r - (n + 1) < r := by omega
    have e : r - (n + 1) + 1 = r - n := by omega
    have hZ' : (C.Z (r - (n + 1) + 1)).PosSemidef := by rw [e]; exact hZ
    have hWk : (C.W (r - (n + 1)) ⊗ₖ (1 : Matrix (Y (r - (n + 1))) (Y (r - (n + 1))) ℂ)).PosSemidef :=
      posSemidef_of_ge hZ' (C.step_out _ hk)
    have hW : (C.W (r - (n + 1))).PosSemidef := psd_of_kron_one hWk
    have hTr := posSemidef_traceRight hW
    refine ⟨posSemidef_of_ge hTr (C.step_in _ hk), fun _ => hW⟩

theorem DualCert.Z_posSemidef [∀ i, Nonempty (Y i)] {r : ℕ}
    {T : Matrix (Hist X Y r) (Hist X Y r) ℂ} {t : ℝ} (C : DualCert r T t)
    (hT : T.PosSemidef) {k : ℕ} (hk : k ≤ r) : (C.Z k).PosSemidef := by
  have := (C.posSemidef_Z hT (r - k) (by omega)).1
  rwa [show r - (r - k) = k by omega] at this

theorem DualCert.W_posSemidef [∀ i, Nonempty (Y i)] {r : ℕ}
    {T : Matrix (Hist X Y r) (Hist X Y r) ℂ} {t : ℝ} (C : DualCert r T t)
    (hT : T.PosSemidef) {k : ℕ} (hk : k < r) : (C.W k).PosSemidef := by
  have := (C.posSemidef_Z hT (r - k) (by omega)).2 (by omega)
  rwa [show r - (r - k) = k by omega] at this

/-! ## The strategy value of a tester -/

/-- The strategy value `sup {Re tr (T Q_r) : IsStrategy r Q}`. -/
noncomputable def sdpVal {r : ℕ} (T : Matrix (Hist X Y r) (Hist X Y r) ℂ) : ℝ :=
  sSup {v | ∃ Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ, IsStrategy r Q ∧
    (trace (T * Q r)).re = v}

theorem sdpVal_nonempty [∀ i, Nonempty (Y i)] {r : ℕ} (T : Matrix (Hist X Y r) (Hist X Y r) ℂ) :
    {v | ∃ Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ, IsStrategy r Q ∧
      (trace (T * Q r)).re = v}.Nonempty :=
  ⟨_, mixedStrategy X Y, mixedStrategy_isStrategy r, rfl⟩

theorem sdpVal_bddAbove {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ} (hT : T.PosSemidef) :
    BddAbove {v | ∃ Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ, IsStrategy r Q ∧
      (trace (T * Q r)).re = v} := by
  refine ⟨(trace T).re * ∏ i ∈ Finset.range r, (Fintype.card (X i) : ℝ), ?_⟩
  rintro v ⟨Q, hQ, rfl⟩
  exact pairing_le_trace_mul_card hT hQ

theorem pairing_le_sdpVal {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ} (hT : T.PosSemidef)
    {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (hQ : IsStrategy r Q) :
    (trace (T * Q r)).re ≤ sdpVal T :=
  le_csSup (sdpVal_bddAbove hT) ⟨Q, hQ, rfl⟩

theorem sdpVal_le_of_cert [∀ i, Nonempty (Y i)] {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ}
    {t : ℝ} (C : DualCert r T t) : sdpVal T ≤ t :=
  csSup_le (sdpVal_nonempty T) fun _ ⟨_, hQ, hv⟩ => hv ▸ C.weak_duality hQ

theorem sdpVal_nonneg [∀ i, Nonempty (Y i)] {r : ℕ} {T : Matrix (Hist X Y r) (Hist X Y r) ℂ}
    (hT : T.PosSemidef) : 0 ≤ sdpVal T :=
  le_trans (Complex.nonneg_iff.mp (psd_trace_mul_nonneg hT
    ((mixedStrategy_isStrategy (X := X) (Y := Y) r).posSemidef r le_rfl))).1
    (pairing_le_sdpVal hT (mixedStrategy_isStrategy r))

/-! ## Joint histories -/

end ShiQIP

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

variable {X₁ Y₁ X₂ Y₂ : ℕ → Type}
variable [∀ i, Fintype (X₁ i)] [∀ i, Fintype (Y₁ i)] [∀ i, Fintype (X₂ i)] [∀ i, Fintype (Y₂ i)]
variable [∀ i, DecidableEq (X₁ i)] [∀ i, DecidableEq (Y₁ i)] [∀ i, DecidableEq (X₂ i)]
  [∀ i, DecidableEq (Y₂ i)]

/-- Joint registers. -/
abbrev PairReg (A B : ℕ → Type) (i : ℕ) : Type := A i × B i

variable (X₁ Y₁ X₂ Y₂) in
/-- **Joint histories are pairs of histories.** -/
def histEquiv : ∀ k, Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k ≃ Hist X₁ Y₁ k × Hist X₂ Y₂ k
  | 0 => (Equiv.uniqueProd Unit Unit).symm
  | k + 1 =>
    ((((histEquiv k).prodCongr (Equiv.refl (X₁ k × X₂ k))).trans
      (Equiv.prodProdProdComm _ _ _ _)).prodCongr (Equiv.refl (Y₁ k × Y₂ k))).trans
      (Equiv.prodProdProdComm _ _ _ _)

variable (X₁ Y₁ X₂ Y₂) in
/-- The identification at the intermediate level `Hist k × X k`. -/
def midEquiv (k : ℕ) : Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k × (X₁ k × X₂ k) ≃
    (Hist X₁ Y₁ k × X₁ k) × (Hist X₂ Y₂ k × X₂ k) :=
  ((histEquiv X₁ Y₁ X₂ Y₂ k).prodCongr (Equiv.refl _)).trans (Equiv.prodProdProdComm _ _ _ _)

theorem midEquiv_apply (k : ℕ) (h : Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k) (x₁ : X₁ k)
    (x₂ : X₂ k) : midEquiv X₁ Y₁ X₂ Y₂ k (h, (x₁, x₂)) =
      (((histEquiv X₁ Y₁ X₂ Y₂ k h).1, x₁), ((histEquiv X₁ Y₁ X₂ Y₂ k h).2, x₂)) := rfl

theorem histEquiv_succ_apply (k : ℕ) (h : Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k) (x₁ : X₁ k)
    (x₂ : X₂ k) (y₁ : Y₁ k) (y₂ : Y₂ k) :
    histEquiv X₁ Y₁ X₂ Y₂ (k + 1) (((h, (x₁, x₂)), (y₁, y₂)) :
        Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) (k + 1)) =
      (((((histEquiv X₁ Y₁ X₂ Y₂ k h).1, x₁), y₁) : Hist X₁ Y₁ (k + 1)),
        ((((histEquiv X₁ Y₁ X₂ Y₂ k h).2, x₂), y₂) : Hist X₂ Y₂ (k + 1))) := rfl

/-- The joint matrix `A ⊗ B` on joint histories. -/
def prodMat {k : ℕ} (A : Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ)
    (B : Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ) :
    Matrix (Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k) (Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k) ℂ :=
  (A ⊗ₖ B).submatrix (histEquiv X₁ Y₁ X₂ Y₂ k) (histEquiv X₁ Y₁ X₂ Y₂ k)

/-- The joint matrix at the intermediate level. -/
def prodMid {k : ℕ} (A : Matrix (Hist X₁ Y₁ k × X₁ k) (Hist X₁ Y₁ k × X₁ k) ℂ)
    (B : Matrix (Hist X₂ Y₂ k × X₂ k) (Hist X₂ Y₂ k × X₂ k) ℂ) :
    Matrix (Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k × (X₁ k × X₂ k))
      (Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k × (X₁ k × X₂ k)) ℂ :=
  (A ⊗ₖ B).submatrix (midEquiv X₁ Y₁ X₂ Y₂ k) (midEquiv X₁ Y₁ X₂ Y₂ k)

theorem prodMat_mul {k : ℕ} (A C : Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ)
    (B D : Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ) :
    prodMat A B * prodMat C D = prodMat (A * C) (B * D) := by
  rw [prodMat, prodMat, submatrix_mul_equiv, ← mul_kronecker_mul]
  rfl

theorem trace_prodMat {k : ℕ} (A : Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ)
    (B : Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ) :
    trace (prodMat A B) = trace A * trace B := by
  rw [prodMat, trace_submatrix_equiv, trace_kronecker]

theorem prodMat_posSemidef {k : ℕ} {A : Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ}
    {B : Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (prodMat A B).PosSemidef :=
  (hA.kronecker hB).submatrix _

theorem prodMat_le {k : ℕ} {A B : Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ}
    {C D : Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hA : A.PosSemidef) (hD : D.PosSemidef) : prodMat A C ≤ prodMat B D :=
  submatrix_le_submatrix (kron_le_kron hAB hCD hA hD) _

theorem traceRight_prodMat_succ {k : ℕ}
    (A : Matrix ((Hist X₁ Y₁ k × X₁ k) × Y₁ k) ((Hist X₁ Y₁ k × X₁ k) × Y₁ k) ℂ)
    (B : Matrix ((Hist X₂ Y₂ k × X₂ k) × Y₂ k) ((Hist X₂ Y₂ k × X₂ k) × Y₂ k) ℂ) :
    traceRight (prodMat (k := k + 1) A B :
      Matrix ((Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k × (X₁ k × X₂ k)) × (Y₁ k × Y₂ k))
        ((Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k × (X₁ k × X₂ k)) × (Y₁ k × Y₂ k)) ℂ) =
      prodMid (traceRight A) (traceRight B) := by
  ext ⟨h, x₁, x₂⟩ ⟨h', x₁', x₂'⟩
  simp only [traceRight_apply, prodMid, submatrix_apply, kroneckerMap_apply, midEquiv_apply,
    Finset.sum_mul_sum]
  change ∑ y : Y₁ k × Y₂ k, (prodMat (k := k + 1) A B) ((h, (x₁, x₂)), y) ((h', (x₁', x₂')), y) = _
  rw [Fintype.sum_prod_type]
  rfl

theorem prodMat_kron_one {k : ℕ} (A : Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ)
    (B : Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ) :
    prodMat A B ⊗ₖ (1 : Matrix (X₁ k × X₂ k) (X₁ k × X₂ k) ℂ) =
      prodMid (A ⊗ₖ (1 : Matrix (X₁ k) (X₁ k) ℂ)) (B ⊗ₖ (1 : Matrix (X₂ k) (X₂ k) ℂ)) := by
  ext ⟨h, x₁, x₂⟩ ⟨h', x₁', x₂'⟩
  simp only [prodMat, prodMid, submatrix_apply, kroneckerMap_apply, midEquiv_apply, one_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

theorem prodMid_kron_one {k : ℕ} (A : Matrix (Hist X₁ Y₁ k × X₁ k) (Hist X₁ Y₁ k × X₁ k) ℂ)
    (B : Matrix (Hist X₂ Y₂ k × X₂ k) (Hist X₂ Y₂ k × X₂ k) ℂ) :
    prodMid A B ⊗ₖ (1 : Matrix (Y₁ k × Y₂ k) (Y₁ k × Y₂ k) ℂ) =
      (prodMat (k := k + 1) (A ⊗ₖ (1 : Matrix (Y₁ k) (Y₁ k) ℂ))
        (B ⊗ₖ (1 : Matrix (Y₂ k) (Y₂ k) ℂ)) :
        Matrix ((Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k × (X₁ k × X₂ k)) × (Y₁ k × Y₂ k))
          ((Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) k × (X₁ k × X₂ k)) × (Y₁ k × Y₂ k)) ℂ) := by
  ext ⟨⟨h, x₁, x₂⟩, y₁, y₂⟩ ⟨⟨h', x₁', x₂'⟩, y₁', y₂'⟩
  change A ((histEquiv X₁ Y₁ X₂ Y₂ k h).1, x₁) ((histEquiv X₁ Y₁ X₂ Y₂ k h').1, x₁') *
      B ((histEquiv X₁ Y₁ X₂ Y₂ k h).2, x₂) ((histEquiv X₁ Y₁ X₂ Y₂ k h').2, x₂') *
      (1 : Matrix (Y₁ k × Y₂ k) (Y₁ k × Y₂ k) ℂ) (y₁, y₂) (y₁', y₂') =
    (A ((histEquiv X₁ Y₁ X₂ Y₂ k h).1, x₁) ((histEquiv X₁ Y₁ X₂ Y₂ k h').1, x₁') *
      (1 : Matrix (Y₁ k) (Y₁ k) ℂ) y₁ y₁') *
    (B ((histEquiv X₁ Y₁ X₂ Y₂ k h).2, x₂) ((histEquiv X₁ Y₁ X₂ Y₂ k h').2, x₂') *
      (1 : Matrix (Y₂ k) (Y₂ k) ℂ) y₂ y₂')
  by_cases e₁ : y₁ = y₁' <;> by_cases e₂ : y₂ = y₂' <;> simp [one_apply, e₁, e₂]

theorem traceRight_prodMid {k : ℕ} (A : Matrix (Hist X₁ Y₁ k × X₁ k) (Hist X₁ Y₁ k × X₁ k) ℂ)
    (B : Matrix (Hist X₂ Y₂ k × X₂ k) (Hist X₂ Y₂ k × X₂ k) ℂ) :
    traceRight (prodMid A B) = prodMat (traceRight A) (traceRight B) := by
  ext h h'
  simp only [traceRight_apply, prodMid, prodMat, submatrix_apply, kroneckerMap_apply,
    midEquiv_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem prodMid_le {k : ℕ} {A B : Matrix (Hist X₁ Y₁ k × X₁ k) (Hist X₁ Y₁ k × X₁ k) ℂ}
    {C D : Matrix (Hist X₂ Y₂ k × X₂ k) (Hist X₂ Y₂ k × X₂ k) ℂ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hA : A.PosSemidef) (hD : D.PosSemidef) : prodMid A C ≤ prodMid B D :=
  submatrix_le_submatrix (kron_le_kron hAB hCD hA hD) _

theorem prodMat_zero_smul_one (c₁ c₂ : ℂ) :
    prodMat (k := 0) (c₁ • (1 : Matrix (Hist X₁ Y₁ 0) (Hist X₁ Y₁ 0) ℂ))
        (c₂ • (1 : Matrix (Hist X₂ Y₂ 0) (Hist X₂ Y₂ 0) ℂ)) =
      (c₁ * c₂) • (1 : Matrix (Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) 0)
        (Hist (PairReg X₁ X₂) (PairReg Y₁ Y₂) 0) ℂ) := by
  ext a b
  obtain rfl : a = b := Subsingleton.elim (α := Unit) a b
  simp [prodMat, one_apply]

/-! ## Products of strategies -/

/-- **Products of strategies are joint strategies.** -/
theorem isStrategy_prod {r : ℕ} {Q₁ : ∀ k, Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ}
    {Q₂ : ∀ k, Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ} (h₁ : IsStrategy r Q₁)
    (h₂ : IsStrategy r Q₂) : IsStrategy r (fun k => prodMat (Q₁ k) (Q₂ k)) where
  zero := by
    rw [h₁.zero, h₂.zero]
    have := prodMat_zero_smul_one (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂) 1 1
    simpa using this
  posSemidef k hk := prodMat_posSemidef (h₁.posSemidef k hk) (h₂.posSemidef k hk)
  causal k hk := by
    have c₁ := h₁.causal k hk
    have c₂ := h₂.causal k hk
    unfold Causal at c₁ c₂ ⊢
    exact (traceRight_prodMat_succ (Q₁ (k + 1)) (Q₂ (k + 1))).trans
      (by rw [c₁, c₂, prodMat_kron_one])

/-- **The pairing factorizes on products.** -/
theorem trace_prodMat_mul {k : ℕ} (A C : Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ)
    (B D : Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ) :
    trace (prodMat A B * prodMat C D) = trace (A * C) * trace (B * D) := by
  rw [prodMat_mul, trace_prodMat]

/-! ## Products of certificates -/

/-- **Tensor product of dual certificates.** -/
noncomputable def DualCert.prod [∀ i, Nonempty (Y₁ i)] [∀ i, Nonempty (Y₂ i)] {r : ℕ}
    {T₁ : Matrix (Hist X₁ Y₁ r) (Hist X₁ Y₁ r) ℂ} {T₂ : Matrix (Hist X₂ Y₂ r) (Hist X₂ Y₂ r) ℂ}
    {t₁ t₂ : ℝ} (C₁ : DualCert r T₁ t₁) (C₂ : DualCert r T₂ t₂) (hT₁ : T₁.PosSemidef)
    (hT₂ : T₂.PosSemidef) : DualCert r (prodMat T₁ T₂) (t₁ * t₂) where
  Z k := prodMat (C₁.Z k) (C₂.Z k)
  W k := prodMid (C₁.W k) (C₂.W k)
  top := prodMat_le C₁.top C₂.top hT₁ (C₂.Z_posSemidef hT₂ le_rfl)
  step_out k hk := by
    rw [prodMid_kron_one]
    exact prodMat_le (k := k + 1) (C₁.step_out k hk) (C₂.step_out k hk)
      (C₁.Z_posSemidef hT₁ hk) ((C₂.W_posSemidef hT₂ hk).kronecker PosSemidef.one)
  step_in k hk := by
    rw [traceRight_prodMid]
    exact prodMat_le (C₁.step_in k hk) (C₂.step_in k hk)
      (posSemidef_traceRight (C₁.W_posSemidef hT₁ hk)) (C₂.Z_posSemidef hT₂ hk.le)
  bottom := by
    have h := prodMat_le C₁.bottom C₂.bottom (C₁.Z_posSemidef hT₁ (Nat.zero_le _))
      (posSemidef_of_ge (C₂.Z_posSemidef hT₂ (Nat.zero_le _)) C₂.bottom)
    rw [prodMat_zero_smul_one] at h
    simpa using h

/-! ## The product theorem -/

theorem re_mul_of_nonneg {z w : ℂ} (hz : 0 ≤ z) : (z * w).re = z.re * w.re := by
  rw [Complex.mul_re, (Complex.nonneg_iff.mp hz).2.symm, zero_mul, sub_zero]

/-- **Product theorem.** The strategy value of the parallel game with all-pass acceptance is
the product of the values. The supremum ranges over **all** joint (entangled) strategies. -/
theorem sdpVal_prod [∀ i, Nonempty (X₁ i)] [∀ i, Nonempty (Y₁ i)] [∀ i, Nonempty (X₂ i)]
    [∀ i, Nonempty (Y₂ i)] {r : ℕ} {T₁ : Matrix (Hist X₁ Y₁ r) (Hist X₁ Y₁ r) ℂ}
    {T₂ : Matrix (Hist X₂ Y₂ r) (Hist X₂ Y₂ r) ℂ} (hT₁ : T₁.PosSemidef)
    (hT₂ : T₂.PosSemidef) : sdpVal (prodMat T₁ T₂) = sdpVal T₁ * sdpVal T₂ := by
  set v₁ := sdpVal T₁
  set v₂ := sdpVal T₂
  have hv₁ : 0 ≤ v₁ := sdpVal_nonneg hT₁
  have hv₂ : 0 ≤ v₂ := sdpVal_nonneg hT₂
  have hT := prodMat_posSemidef hT₁ hT₂
  refine le_antisymm ?_ ?_
  · -- upper bound by tensored approximate certificates
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set η : ℝ := min 1 (ε / (v₁ + v₂ + 1))
    have hη : 0 < η := lt_min one_pos (div_pos hε (by linarith))
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηε : η * (v₁ + v₂ + 1) ≤ ε := by
      have := min_le_right 1 (ε / (v₁ + v₂ + 1))
      rwa [le_div_iff₀ (by linarith)] at this
    obtain ⟨t₁, ht₁, ⟨C₁⟩⟩ := exists_dualCert_le hT₁.isHermitian
      (fun Q hQ => pairing_le_sdpVal hT₁ hQ) hη
    obtain ⟨t₂, ht₂, ⟨C₂⟩⟩ := exists_dualCert_le hT₂.isHermitian
      (fun Q hQ => pairing_le_sdpVal hT₂ hQ) hη
    have h0₁ : v₁ ≤ t₁ := sdpVal_le_of_cert C₁
    have h0₂ : v₂ ≤ t₂ := sdpVal_le_of_cert C₂
    have hP := sdpVal_le_of_cert (C₁.prod C₂ hT₁ hT₂)
    have : t₁ * t₂ ≤ (v₁ + η) * (v₂ + η) :=
      mul_le_mul ht₁ ht₂ (by linarith) (by linarith)
    nlinarith
  · -- lower bound by product strategies
    have key : ∀ Q₁ : ∀ k, Matrix (Hist X₁ Y₁ k) (Hist X₁ Y₁ k) ℂ, IsStrategy r Q₁ →
        ∀ Q₂ : ∀ k, Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ, IsStrategy r Q₂ →
          (trace (T₁ * Q₁ r)).re * (trace (T₂ * Q₂ r)).re ≤ sdpVal (prodMat T₁ T₂) := by
      intro Q₁ h₁ Q₂ h₂
      have := pairing_le_sdpVal hT (isStrategy_prod h₁ h₂)
      rwa [trace_prodMat_mul, re_mul_of_nonneg (psd_trace_mul_nonneg hT₁ (h₁.posSemidef r le_rfl))] at this
    set s := sdpVal (prodMat T₁ T₂)
    have hs : 0 ≤ s := sdpVal_nonneg hT
    -- first: v₁ * p₂ ≤ s for every attainable p₂
    have step : ∀ Q₂ : ∀ k, Matrix (Hist X₂ Y₂ k) (Hist X₂ Y₂ k) ℂ, IsStrategy r Q₂ →
        v₁ * (trace (T₂ * Q₂ r)).re ≤ s := by
      intro Q₂ h₂
      set p₂ := (trace (T₂ * Q₂ r)).re
      have hp₂ : 0 ≤ p₂ :=
        (Complex.nonneg_iff.mp (psd_trace_mul_nonneg hT₂ (h₂.posSemidef r le_rfl))).1
      rcases hp₂.eq_or_lt with h | h
      · rw [← h, mul_zero]; exact hs
      · have : v₁ ≤ s / p₂ := csSup_le (sdpVal_nonempty T₁) fun _ ⟨Q₁, h₁, hv⟩ => by
          rw [← hv, le_div_iff₀ h]; exact key Q₁ h₁ Q₂ h₂
        rwa [le_div_iff₀ h] at this
    rcases hv₁.eq_or_lt with h | h
    · rw [← h, zero_mul]; exact hs
    · have : v₂ ≤ s / v₁ := csSup_le (sdpVal_nonempty T₂) fun _ ⟨Q₂, h₂, hv⟩ => by
        rw [← hv, le_div_iff₀ h, mul_comm]; exact step Q₂ h₂
      rwa [le_div_iff₀ h, mul_comm] at this

/-! ## Verifiers -/

/-- **The game value of a verifier is the strategy value of its tester.** -/
theorem value_eq_sdpVal (d : Desc) : value d = sdpVal (tester d) := by
  refine le_antisymm ?_ (csSup_le (sdpVal_nonempty _) fun _ ⟨Q, hQ, hv⟩ =>
    hv ▸ pairing_le_value hQ)
  obtain ⟨P, hP⟩ := value_attained d
  rw [← hP, accept_eq_pairing]
  exact pairing_le_sdpVal (tester_posSemidef d) (opStrategy_isStrategy P)

end ShiQIP
