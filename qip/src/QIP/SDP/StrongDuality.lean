/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.SDP.WeakDuality
import QIP.SDP.ConicDuality

/-!
# Q23 — strong duality for the strategy SDP (approximate certificates)

**Main theorem.** `exists_dualCert_le` takes a PSD objective `T`, an upper bound `V` on
`Re tr (T Q_r)` over causal strategies, and `η > 0`. It returns an actual matrix certificate
`DualCert r T t` (the dual of Q22) with `t ≤ V + η`. The registers must be nonempty.

**Corollary.** `exists_dualCert_value` specializes to the tester of a verifier: for every
`η > 0` there is a certificate whose bound is within `η` of `value d`. So the bounds of Q22 are
tight in the limit: `value_eq_iInf_cert`.

The proof instantiates `ShiQuantum.conic_approx_duality`, which rests on Mathlib's Hahn–Banach
separation, on the real vector spaces of matrix families. The inputs are:

* **the cone** `psdCone`: families of PSD matrices. It is convex and closed under nonnegative
  scaling.
* **the constraint map** `constrMap Q = (causalMap Q, Q_0)` and right-hand side `(0, 1)`.
  Feasibility is exactly `IsStrategy` (`isStrategy_iff_causalMap`).
* **the coercive gauge** `gauge Q = Σ_k Re tr Q_k / P_k`, where `P_k = ∏_{i<k} |X_i|`. Its
  truncations are compact (`isCompact_gauge_le`), because entries of PSD matrices are bounded
  by their trace.
* **an explicit dominating dual direction** `posDir`, with weights `(r−k)/P_{k+1}` and `r+1`.
  The identity `posDir (constrMap Q) = gauge Q` is a summation by parts (`telescope`).
* **a strictly feasible primal point**, `mixedStrategy`: `Q_k = 1/∏_{i<k}|Y_i| · 1`. It is
  positive definite (`mixedStrategy_posDef`), being the strategy that answers with uniformly
  random outputs.

The resulting real functional is converted into matrices by trace duality on Hermitian
matrices (`exists_herm_rep`). The resulting inequalities are turned into PSD order statements
by `posSemidef_of_trace_nonneg`.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Matrix spaces are locally convex -/

instance matrix_locallyConvexSpace {m n : Type*} :
    LocallyConvexSpace ℝ (Matrix m n ℂ) :=
  inferInstanceAs (LocallyConvexSpace ℝ (m → n → ℂ))

/-! ## Trace duality on Hermitian matrices -/

theorem single_eq_re_smul_add {n : Type} [DecidableEq n] (i j : n) (z : ℂ) :
    single i j z = z.re • single i j (1 : ℂ) + z.im • single i j Complex.I := by
  ext a b
  simp only [single_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  split_ifs
  · rw [mul_one]; exact (Complex.re_add_im z).symm
  · simp

/-- Every real-linear functional on complex matrices is `M ↦ Re tr (W M)`. -/
theorem exists_trace_rep {n : Type} [Fintype n] [DecidableEq n]
    (φ : Matrix n n ℂ →ₗ[ℝ] ℝ) : ∃ W : Matrix n n ℂ, ∀ M, φ M = (trace (W * M)).re := by
  refine ⟨Matrix.of fun j i => (φ (single i j 1) : ℂ) - Complex.I * φ (single i j Complex.I),
    fun M => ?_⟩
  conv_lhs => rw [matrix_eq_sum_single M]
  simp only [map_sum, trace, diag_apply, mul_apply, of_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [single_eq_re_smul_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- On Hermitian arguments the representing matrix can be taken Hermitian. -/
theorem exists_herm_rep {n : Type} [Fintype n] [DecidableEq n]
    (φ : Matrix n n ℂ →ₗ[ℝ] ℝ) :
    ∃ W : Matrix n n ℂ, W.IsHermitian ∧ ∀ M, M.IsHermitian → φ M = (trace (W * M)).re := by
  obtain ⟨W₀, hW₀⟩ := exists_trace_rep φ
  refine ⟨(1 / 2 : ℝ) • (W₀ + W₀ᴴ), ?_, fun M hM => ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_smul, star_trivial, conjTranspose_add, conjTranspose_conjTranspose,
      add_comm]
  · have h : (trace (W₀ᴴ * M)).re = (trace (W₀ * M)).re := by
      have : W₀ᴴ * M = (M * W₀)ᴴ := by rw [conjTranspose_mul, hM.eq]
      rw [this, trace_conjTranspose, trace_mul_comm, Complex.star_def, Complex.conj_re]
    rw [hW₀, Matrix.smul_mul, Matrix.add_mul, trace_smul, trace_add, Complex.smul_re,
      Complex.add_re, h]
    ring

/-- A Hermitian matrix with nonnegative trace pairing against every PSD matrix is PSD. -/
theorem posSemidef_of_trace_nonneg {n : Type} [Fintype n] [DecidableEq n] {D : Matrix n n ℂ}
    (hD : D.IsHermitian) (h : ∀ P : Matrix n n ℂ, P.PosSemidef → 0 ≤ (trace (D * P)).re) :
    D.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨hD, fun x => ?_⟩
  have h1 := h _ (posSemidef_vecMulVec_self_star x)
  rw [trace_mul_rankOne] at h1
  have h2 : (star x ⬝ᵥ D *ᵥ x).im = 0 := hD.im_star_dotProduct_mulVec_self x
  exact Complex.nonneg_iff.mpr ⟨h1, h2.symm⟩

/-- `A ≤ B` from the trace pairing, for Hermitian `A`, `B`. -/
theorem le_of_trace_le {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ P : Matrix n n ℂ, P.PosSemidef → (trace (A * P)).re ≤ (trace (B * P)).re) : A ≤ B := by
  rw [Matrix.le_iff]
  refine posSemidef_of_trace_nonneg (hB.sub hA) fun P hP => ?_
  rw [Matrix.sub_mul, trace_sub, Complex.sub_re]
  linarith [h P hP]

/-! ## The strategy SDP as a conic program -/

theorem telescope (s : ℕ → ℝ) : ∀ r : ℕ,
    ∑ k ∈ Finset.range r, ((r : ℝ) - k) * (s (k + 1) - s k) + ((r : ℝ) + 1) * s 0 =
      ∑ j ∈ Finset.range (r + 1), s j
  | 0 => by simp
  | r + 1 => by
    have ih := telescope s r
    have e : ∑ k ∈ Finset.range (r + 1), (((r + 1 : ℕ) : ℝ) - k) * (s (k + 1) - s k) =
        ∑ k ∈ Finset.range (r + 1), ((r : ℝ) - k) * (s (k + 1) - s k) +
          ∑ k ∈ Finset.range (r + 1), (s (k + 1) - s k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    rw [e, Finset.sum_range_sub, Finset.sum_range_succ (fun k => ((r : ℝ) - k) * _),
      Finset.sum_range_succ (fun j => s j) (r + 1), ← ih]
    push_cast; ring

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

variable (X) in
/-- `P_k = ∏_{i<k} |X_i|`. -/
noncomputable def cardProd (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (Fintype.card (X i) : ℝ)

omit [∀ i, DecidableEq (X i)] in
theorem cardProd_succ (k : ℕ) : cardProd X (k + 1) = cardProd X k * Fintype.card (X k) :=
  Finset.prod_range_succ _ _

omit [∀ i, DecidableEq (X i)] in
theorem cardProd_pos [∀ i, Nonempty (X i)] (k : ℕ) : 0 < cardProd X k :=
  Finset.prod_pos fun _ _ => Nat.cast_pos.mpr Fintype.card_pos

variable (X Y) in
/-- The PSD cone of primal variables. -/
def psdCone (r : ℕ) : Set (PrimalVar X Y r) := {Q | ∀ k, (Q k).PosSemidef}

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem psdCone_smul {r : ℕ} {Q : PrimalVar X Y r} (hQ : Q ∈ psdCone X Y r) (t : ℝ)
    (ht : 0 ≤ t) : t • Q ∈ psdCone X Y r :=
  fun k => (hQ k).smul ht

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem convex_psdCone (r : ℕ) : Convex ℝ (psdCone X Y r) := by
  intro Q hQ Q' hQ' a b ha hb _ k
  exact ((hQ k).smul ha).add ((hQ' k).smul hb)

omit [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem isClosed_psdCone (r : ℕ) : IsClosed (psdCone X Y r) := by
  have : psdCone X Y r = ⋂ k, (fun Q : PrimalVar X Y r => Q k) ⁻¹' {M | M.PosSemidef} := by
    ext Q; simp [psdCone]
  rw [this]
  exact isClosed_iInter fun k => (isClosed_posSemidef).preimage (continuous_apply k)

variable (X Y) in
/-- The constraint space: causal residuals and the turn-`0` matrix. -/
abbrev ConstrSpace (r : ℕ) := ConstrVar X Y r × Matrix (Hist X Y 0) (Hist X Y 0) ℂ

/-- `Q_0` viewed on `Hist 0`. -/
def zeroView {r : ℕ} (Q : PrimalVar X Y r) : Matrix (Hist X Y 0) (Hist X Y 0) ℂ :=
  Q ⟨0, Nat.succ_pos r⟩

/-- `Q_r` viewed on `Hist r`. -/
def lastView {r : ℕ} (Q : PrimalVar X Y r) : Matrix (Hist X Y r) (Hist X Y r) ℂ :=
  Q (Fin.last r)

variable (X Y) in
/-- The constraint map `Q ↦ (causalMap Q, Q_0)`. -/
noncomputable def constrMap (r : ℕ) : PrimalVar X Y r →ₗ[ℝ] ConstrSpace X Y r :=
  (causalMap X Y r).prod
    { toFun := zeroView
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [∀ i, Fintype (X i)] [∀ i, DecidableEq (Y i)] in
theorem constrMap_apply {r : ℕ} (Q : PrimalVar X Y r) :
    constrMap X Y r Q = (causalMap X Y r Q, zeroView Q) := rfl

omit [∀ i, Fintype (X i)] [∀ i, DecidableEq (Y i)] in
theorem continuous_constrMap (r : ℕ) : Continuous (constrMap X Y r) := by
  refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_apply _)
  change Continuous fun Q : PrimalVar X Y r => causalRes Q k
  unfold causalRes succView castView
  exact (continuous_traceRight.comp (continuous_apply _)).sub
    (continuous_kronecker_one.comp (continuous_apply _))

variable (X Y) in
/-- The objective `Q ↦ Re tr (T Q_r)`. -/
noncomputable def objMap (r : ℕ) (T : Matrix (Hist X Y r) (Hist X Y r) ℂ) :
    PrimalVar X Y r →ₗ[ℝ] ℝ where
  toFun Q := (trace (T * lastView Q)).re
  map_add' Q Q' := by
    change (trace (T * (lastView Q + lastView Q'))).re = _
    rw [Matrix.mul_add, trace_add, Complex.add_re]
  map_smul' c Q := by
    change (trace (T * (c • lastView Q))).re = _
    rw [Matrix.mul_smul, trace_smul, Complex.smul_re, RingHom.id_apply, smul_eq_mul]

omit [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem objMap_apply {r : ℕ} (T : Matrix (Hist X Y r) (Hist X Y r) ℂ) (Q : PrimalVar X Y r) :
    objMap X Y r T Q = (trace (T * lastView Q)).re := rfl

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem lastView_single_last {r : ℕ} (P : Matrix (Hist X Y r) (Hist X Y r) ℂ) :
    lastView (Pi.single (Fin.last r) P : PrimalVar X Y r) = P := Pi.single_eq_same _ _

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem lastView_single_ne {r : ℕ} {j : Fin (r + 1)} (hj : Fin.last r ≠ j)
    (P : Matrix (Hist X Y j) (Hist X Y j) ℂ) :
    lastView (Pi.single j P : PrimalVar X Y r) = 0 := Pi.single_eq_of_ne hj _

omit [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem continuous_objMap (r : ℕ) (T : Matrix (Hist X Y r) (Hist X Y r) ℂ) :
    Continuous (objMap X Y r T) :=
  Complex.continuous_re.comp ((continuous_const.matrix_mul (continuous_apply _)).matrix_trace)

variable (X Y) in
/-- The coercive gauge `Σ_k Re tr Q_k / P_k`. -/
noncomputable def gauge (r : ℕ) : PrimalVar X Y r →ₗ[ℝ] ℝ where
  toFun Q := ∑ k : Fin (r + 1), (trace (Q k)).re / cardProd X k
  map_add' Q Q' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, trace_add, Complex.add_re, add_div]
  map_smul' c Q := by
    rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, trace_smul, Complex.smul_re, smul_eq_mul, mul_div_assoc]

omit [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem gauge_apply {r : ℕ} (Q : PrimalVar X Y r) :
    gauge X Y r Q = ∑ k : Fin (r + 1), (trace (Q k)).re / cardProd X k := rfl

omit [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem gauge_nonneg [∀ i, Nonempty (X i)] {r : ℕ} (Q : PrimalVar X Y r)
    (hQ : Q ∈ psdCone X Y r) : 0 ≤ gauge X Y r Q :=
  (gauge_apply Q).symm ▸
  Finset.sum_nonneg fun k _ =>
    div_nonneg (Complex.nonneg_iff.mp (hQ k).trace_nonneg).1 (cardProd_pos k).le

omit [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem continuous_gauge (r : ℕ) : Continuous (gauge X Y r) :=
  show Continuous fun Q : PrimalVar X Y r => ∑ k : Fin (r + 1), (trace (Q k)).re / cardProd X k from
  continuous_finsetSum _ fun k _ =>
    (Complex.continuous_re.comp ((continuous_apply k).matrix_trace)).div_const _

theorem isCompact_gauge_le [∀ i, Nonempty (X i)] (r : ℕ) (R : ℝ) :
    IsCompact (psdCone X Y r ∩ {Q | gauge X Y r Q ≤ R}) := by
  refine (isCompact_univ_pi fun k : Fin (r + 1) => isCompact_entryBox (n := Hist X Y k)
    (R * cardProd X k)).of_isClosed_subset
    ((isClosed_psdCone r).inter (isClosed_le (continuous_gauge r) continuous_const)) ?_
  rintro Q ⟨hQ, hR⟩ k -
  intro i j
  have hk : (trace (Q k)).re / cardProd X k ≤ R := by
    refine le_trans ?_ hR
    exact Finset.single_le_sum (f := fun k : Fin (r + 1) => (trace (Q k)).re / cardProd X k)
      (fun k _ => div_nonneg (Complex.nonneg_iff.mp (hQ k).trace_nonneg).1
        (cardProd_pos k).le) (Finset.mem_univ k)
  rw [div_le_iff₀ (cardProd_pos k)] at hk
  exact (norm_apply_le_trace (hQ k) i j).trans hk

variable (X Y) in
/-- The dominating dual direction: weights `(r − k)/P_{k+1}` and `r + 1`. -/
noncomputable def posDir (r : ℕ) : ConstrSpace X Y r →ₗ[ℝ] ℝ where
  toFun p := ∑ k : Fin r, ((r : ℝ) - k) / cardProd X (k + 1) * (trace (p.1 k)).re +
    ((r : ℝ) + 1) * (trace p.2).re
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, trace_add, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, trace_smul, Complex.smul_re,
      smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by ring
    · ring

omit [∀ i, DecidableEq (Y i)] in
theorem trace_causalRes {r : ℕ} (Q : PrimalVar X Y r) (k : Fin r) :
    trace (causalRes Q k) = trace (Q k.succ) - trace (Q k.castSucc) * Fintype.card (X k) := by
  rw [causalRes, trace_sub, trace_traceRight, trace_kronecker, trace_one]
  rfl

omit [∀ i, DecidableEq (Y i)] in
/-- **The dominating direction equals the gauge on the constraint image** (summation by
parts). -/
theorem posDir_constrMap [∀ i, Nonempty (X i)] {r : ℕ} (Q : PrimalVar X Y r) :
    posDir X Y r (constrMap X Y r Q) = gauge X Y r Q := by
  set s : ℕ → ℝ := fun j => if h : j < r + 1 then (trace (Q ⟨j, h⟩)).re / cardProd X j else 0
  have hs : ∀ k : Fin (r + 1), s k = (trace (Q k)).re / cardProd X k := by
    intro k; simp only [s, dif_pos k.isLt]
  have hg : gauge X Y r Q = ∑ j ∈ Finset.range (r + 1), s j := by
    rw [gauge_apply, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => (hs k).symm
  have hterm : ∀ k : Fin r, ((r : ℝ) - k) / cardProd X (k + 1) *
      (trace (causalRes Q k)).re = ((r : ℝ) - k) * (s (k + 1) - s k) := by
    intro k
    have h1 := hs k.succ
    have h2 := hs k.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    rw [h1, h2, trace_causalRes, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, mul_zero, sub_zero, cardProd_succ]
    have hP := (cardProd_pos (X := X) k).ne'
    have hX : (Fintype.card (X k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  have h0 : (trace (zeroView Q)).re = s 0 := by
    simp only [s, dif_pos (Nat.succ_pos r), cardProd, Finset.range_zero, Finset.prod_empty,
      div_one]
    rfl
  change ∑ k : Fin r, ((r : ℝ) - k) / cardProd X (k + 1) * (trace (causalRes Q k)).re +
    ((r : ℝ) + 1) * (trace (zeroView Q)).re = _
  rw [hg, Finset.sum_congr rfl fun k _ => hterm k, h0,
    Fin.sum_univ_eq_sum_range (fun k => ((r : ℝ) - k) * (s (k + 1) - s k)), telescope]

/-! ## A strictly feasible strategy -/

variable (X Y) in
/-- The strategy answering with uniformly random outputs: `Q_k = (∏_{i<k} |Y_i|)⁻¹ · 1`. -/
noncomputable def mixedStrategy (k : ℕ) : Matrix (Hist X Y k) (Hist X Y k) ℂ :=
  (((cardProd Y k)⁻¹ : ℝ) : ℂ) • 1

omit [∀ i, Fintype (X i)] in
/-- **Strict feasibility**: every prefix of `mixedStrategy` is positive definite. -/
theorem mixedStrategy_posDef [∀ i, Nonempty (Y i)] (k : ℕ) :
    (mixedStrategy X Y k).PosDef := by
  rw [mixedStrategy, Complex.coe_smul]
  exact PosDef.one.smul (inv_pos.mpr (cardProd_pos k))

theorem mixedStrategy_isStrategy [∀ i, Nonempty (Y i)] (r : ℕ) :
    IsStrategy r (mixedStrategy X Y) where
  zero := by simp [mixedStrategy, cardProd]
  posSemidef k _ := (mixedStrategy_posDef k).posSemidef
  causal k _ := by
    unfold Causal
    change traceRight ((((cardProd Y (k + 1))⁻¹ : ℝ) : ℂ) •
      (1 : Matrix ((Hist X Y k × X k) × Y k) ((Hist X Y k × X k) × Y k) ℂ)) =
        ((((cardProd Y k)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Hist X Y k) (Hist X Y k) ℂ)) ⊗ₖ
          (1 : Matrix (X k) (X k) ℂ)
    rw [traceRight_smul_one, kron_smul_one, cardProd_succ]
    congr 1
    have hP := (cardProd_pos (X := Y) k).ne'
    have hY : (Fintype.card (Y k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    push_cast
    field_simp

/-! ## From a dual functional to a matrix certificate -/

section Extract

variable {r : ℕ} (y : ConstrSpace X Y r →ₗ[ℝ] ℝ)

/-- The part of `y` on the `k`-th causal residual. -/
noncomputable def slotFun (k : Fin r) :
    Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ →ₗ[ℝ] ℝ :=
  y ∘ₗ LinearMap.inl ℝ _ _ ∘ₗ
    LinearMap.single ℝ (fun k : Fin r => Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ) k

/-- The part of `y` on the turn-`0` matrix. -/
noncomputable def zeroFun : Matrix (Hist X Y 0) (Hist X Y 0) ℂ →ₗ[ℝ] ℝ :=
  y ∘ₗ LinearMap.inr ℝ _ _

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem constrSpace_decomp (p : ConstrSpace X Y r) :
    y p = ∑ k : Fin r, slotFun y k (p.1 k) + zeroFun y p.2 := by
  simp only [slotFun, zeroFun, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, LinearMap.coe_single]
  rw [← map_sum, ← map_add]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, Prod.fst_sum, add_zero]
    exact (Finset.univ_sum_single p.1).symm
  · simp [Prod.snd_sum]

/-- The Hermitian multiplier of the `k`-th causal constraint. -/
noncomputable def multW (k : Fin r) : Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ :=
  (exists_herm_rep (slotFun y k)).choose

/-- The Hermitian multiplier of the constraint `Q_0 = 1`. -/
noncomputable def multZero : Matrix (Hist X Y 0) (Hist X Y 0) ℂ :=
  (exists_herm_rep (zeroFun y)).choose

theorem multW_spec (k : Fin r) : (multW y k).IsHermitian ∧
    ∀ M, M.IsHermitian → slotFun y k M = (trace (multW y k * M)).re :=
  (exists_herm_rep (slotFun y k)).choose_spec

theorem multZero_spec : (multZero y).IsHermitian ∧
    ∀ M, M.IsHermitian → zeroFun y M = (trace (multZero y * M)).re :=
  (exists_herm_rep (zeroFun y)).choose_spec

/-- The multipliers extended by `0` to all `k`. -/
noncomputable def certW (k : ℕ) : Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ :=
  if h : k < r then multW y ⟨k, h⟩ else 0

/-- The certificate matrices `Z_0 = multZero`, `Z_{k+1} = W_k ⊗ 1`. -/
noncomputable def certZ : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ
  | 0 => multZero y
  | k + 1 => certW y k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ)

theorem certW_of_lt (k : Fin r) : certW y k = multW y k := by
  simp [certW, k.isLt]

theorem certW_self : certW y r = 0 := by simp [certW]

theorem certW_isHermitian (k : ℕ) : (certW y k).IsHermitian := by
  unfold certW
  split_ifs
  · exact (multW_spec y _).1
  · exact isHermitian_zero

theorem certZ_isHermitian : ∀ k, (certZ y k).IsHermitian
  | 0 => (multZero_spec y).1
  | k + 1 => by
    change (certW y k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ))ᴴ = certW y k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ)
    rw [conjTranspose_kronecker, conjTranspose_one, (certW_isHermitian y k).eq]

theorem traceRight_certW_isHermitian (k : ℕ) : (traceRight (certW y k)).IsHermitian := by
  unfold IsHermitian
  rw [traceRight_conjTranspose, (certW_isHermitian y k).eq]

theorem traceRight_zero' {α β : Type} [Fintype β] :
    traceRight (0 : Matrix (α × β) (α × β) ℂ) = 0 := by
  ext a b; simp

/-- **The Lagrangian in slot form**: on Hermitian families,
`y (constrMap Q) = Σ_j Re tr ((Z_j − Tr W_j) Q_j)`. -/
theorem dual_slot_form {Q : PrimalVar X Y r} (hQ : ∀ k, (Q k).IsHermitian) :
    y (constrMap X Y r Q) =
      ∑ j : Fin (r + 1), (trace ((certZ y j - traceRight (certW y j)) * Q j)).re := by
  rw [constrSpace_decomp, constrMap_apply]
  simp only
  rw [Finset.sum_congr rfl fun k _ =>
      (multW_spec y k).2 _ (causalMap_isHermitian hQ k),
    (multZero_spec y).2 _ (hQ _), pairing_causalMap]
  simp only [Matrix.sub_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_succ (fun j => (trace (certZ y j * Q j)).re),
    Fin.sum_univ_castSucc (fun j => (trace (traceRight (certW y j) * Q j)).re)]
  have hlast : (trace (traceRight (certW y (Fin.last r : ℕ)) * Q (Fin.last r))).re = 0 := by
    have h0 : certW y (Fin.last r : ℕ) = 0 := certW_self y
    rw [h0, traceRight_zero', Matrix.zero_mul, trace_zero,
      Complex.zero_re]
  have hsucc : ∀ k : Fin r, (trace (certZ y (k.succ : ℕ) * Q k.succ)).re =
      (trace ((multW y k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ)) * succView Q k)).re := by
    intro k
    change (trace ((certW y k ⊗ₖ (1 : Matrix (Y k) (Y k) ℂ)) * succView Q k)).re = _
    rw [certW_of_lt]
  have hcast : ∀ k : Fin r, (trace (traceRight (certW y (k.castSucc : ℕ)) * Q k.castSucc)).re =
      (trace (traceRight (multW y k) * castView Q k)).re := by
    intro k
    change (trace (traceRight (certW y k) * castView Q k)).re = _
    rw [certW_of_lt]
  rw [hlast, add_zero, Finset.sum_congr rfl fun k _ => hsucc k,
    Finset.sum_congr rfl fun k _ => hcast k]
  change _ = (trace (multZero y * zeroView Q)).re + _ - _
  ring

omit [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] in
theorem single_mem_psdCone (j : Fin (r + 1)) {P : Matrix (Hist X Y j) (Hist X Y j) ℂ}
    (hP : P.PosSemidef) :
    (Pi.single j P : PrimalVar X Y r) ∈ psdCone X Y r := by
  intro k
  by_cases h : k = j
  · subst h; rw [Pi.single_eq_same]; exact hP
  · rw [Pi.single_eq_of_ne h]; exact PosSemidef.zero

theorem dual_single (j : Fin (r + 1)) {P : Matrix (Hist X Y j) (Hist X Y j) ℂ}
    (hP : P.PosSemidef) :
    y (constrMap X Y r (Pi.single j P)) =
      (trace ((certZ y j - traceRight (certW y j)) * P)).re := by
  rw [dual_slot_form y fun k => (single_mem_psdCone j hP k).isHermitian,
    Finset.sum_eq_single j (fun k _ hk => by
      rw [Pi.single_eq_of_ne hk, Matrix.mul_zero, trace_zero, Complex.zero_re])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]

end Extract

/-! ## Strong duality -/

/-- **Approximate strong duality for the strategy SDP.** If `V` bounds `Re tr (T Q_r)` over
all causal strategies, then for every `η > 0` some dual certificate has objective
`t ≤ V + η`. -/
theorem exists_dualCert_le [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)] {r : ℕ}
    {T : Matrix (Hist X Y r) (Hist X Y r) ℂ} (hT : T.IsHermitian) {V : ℝ}
    (hV : ∀ Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ, IsStrategy r Q →
      (trace (T * Q r)).re ≤ V)
    {η : ℝ} (hη : 0 < η) : ∃ t, t ≤ V + η ∧ Nonempty (DualCert r T t) := by
  -- primal facts in conic form
  have hV' : ∀ Q ∈ psdCone X Y r, constrMap X Y r Q = (0, 1) → objMap X Y r T Q ≤ V := by
    intro Q hQ hAQ
    set Qn : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ :=
      fun k => if h : k < r + 1 then Q ⟨k, h⟩ else 0
    have hQn : toPrimal r Qn = Q := by
      funext k; simp only [toPrimal, Qn, dif_pos k.isLt]
    have hc : causalMap X Y r Q = 0 := congrArg Prod.fst hAQ
    have h0 : zeroView Q = 1 := congrArg Prod.snd hAQ
    have hS : IsStrategy r Qn := by
      refine isStrategy_iff_causalMap.mpr ⟨?_, fun k hk => ?_, by rw [hQn]; exact hc⟩
      · simp only [Qn, dif_pos (Nat.succ_pos r)]; exact h0
      · simp only [Qn, dif_pos (Nat.lt_succ_of_le hk)]; exact hQ _
    have := hV Qn hS
    simp only [Qn, dif_pos (Nat.lt_succ_self r)] at this
    exact this
  have hxf : toPrimal r (mixedStrategy X Y) ∈ psdCone X Y r :=
    fun k => (mixedStrategy_posDef k).posSemidef
  have hAxf : constrMap X Y r (toPrimal r (mixedStrategy X Y)) = (0, 1) := by
    obtain ⟨h0, -, hc⟩ := isStrategy_iff_causalMap.mp (mixedStrategy_isStrategy (X := X) (Y := Y) r)
    rw [constrMap_apply, hc]
    exact Prod.ext rfl h0
  obtain ⟨y, hy, hyb⟩ := conic_approx_duality (convex_psdCone r)
    (fun Q hQ t ht => psdCone_smul hQ t ht) (constrMap X Y r) (continuous_constrMap r) (0, 1)
    (objMap X Y r T) (gauge X Y r) (continuous_objMap r T) gauge_nonneg (isCompact_gauge_le r)
    (posDir X Y r) (fun Q _ => (posDir_constrMap Q).ge) hV' hxf hAxf hη
  -- slot inequalities
  have hlast : ∀ P : Matrix (Hist X Y r) (Hist X Y r) ℂ, P.PosSemidef →
      (trace (T * P)).re ≤ (trace (certZ y r * P)).re := by
    intro P hP
    have h := hy _ (single_mem_psdCone (Fin.last r) hP)
    rw [dual_single y (Fin.last r) hP] at h
    have h0 : certW y (Fin.last r : ℕ) = 0 := certW_self y
    rw [objMap_apply, lastView_single_last, h0, traceRight_zero', sub_zero] at h
    exact h
  have hlt : ∀ k < r, ∀ P : Matrix (Hist X Y k) (Hist X Y k) ℂ, P.PosSemidef →
      (trace (traceRight (certW y k) * P)).re ≤ (trace (certZ y k * P)).re := by
    intro k hk P hP
    set j : Fin (r + 1) := ⟨k, by omega⟩
    have hj : Fin.last r ≠ j := fun h => by
      have := congrArg Fin.val h; simp [j] at this; omega
    have h := hy _ (single_mem_psdCone j hP)
    rw [dual_single y j hP] at h
    rw [objMap_apply, lastView_single_ne hj, Matrix.mul_zero, trace_zero, Complex.zero_re, Matrix.sub_mul,
      trace_sub, Complex.sub_re] at h
    change 0 ≤ (trace (certZ y k * P)).re - (trace (traceRight (certW y k) * P)).re at h
    linarith
  -- the objective
  have hU : ∀ a b : Hist X Y 0, a = b := fun a b => Subsingleton.elim (α := Unit) a b
  have hyb' : y (0, 1) = (trace (multZero y)).re := by
    rw [constrSpace_decomp]
    simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add]
    rw [(multZero_spec y).2 _ isHermitian_one, Matrix.mul_one]
  refine ⟨y (0, 1), hyb, ⟨{
    Z := certZ y
    W := certW y
    top := le_of_trace_le hT (certZ_isHermitian y r) hlast
    step_out := fun k _ => le_rfl
    step_in := fun k hk => le_of_trace_le (traceRight_certW_isHermitian y k)
      (certZ_isHermitian y k) (hlt k hk)
    bottom := le_of_eq ?_ }⟩⟩
  change multZero y = _
  ext a b
  obtain rfl := hU a b
  have htr : trace (multZero y) = multZero y a a := by
    have : Unique (Hist X Y 0) := inferInstanceAs (Unique Unit)
    rw [trace, Fintype.sum_unique, diag_apply]
    congr 2
  rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, hyb', htr]
  exact ((multZero_spec y).1.coe_re_apply_self a).symm

/-! ## The verifier's game value -/

instance reg_nonempty (d : Desc) (j : ℕ) : Nonempty (Reg d j) := ⟨fun _ => false⟩

/-- Every causal strategy pairs with the tester to at most the game value. -/
theorem pairing_le_value {d : Desc}
    {Q : ∀ k, Matrix (Hist (Reg d) (Reg d) k) (Hist (Reg d) (Reg d) k) ℂ}
    (hQ : IsStrategy d.numMsgs Q) : (trace (tester d * Q d.numMsgs)).re ≤ value d := by
  obtain ⟨S, -, hS⟩ := exists_opStrategy_of_isStrategy hQ
  rw [← hS _ le_rfl, ← accept_eq_pairing (d := d) S]
  exact accept_le_value d S

/-- **Q23 for verifiers**: for every `η > 0` some dual certificate for the tester bounds every
prover by at most `value d + η`. -/
theorem exists_dualCert_value (d : Desc) {η : ℝ} (hη : 0 < η) :
    ∃ t, value d ≤ t ∧ t ≤ value d + η ∧ Nonempty (DualCert d.numMsgs (tester d) t) := by
  obtain ⟨t, ht, ⟨C⟩⟩ := exists_dualCert_le (tester_posSemidef d).isHermitian
    (fun Q hQ => pairing_le_value hQ) hη
  exact ⟨t, C.value_le, ht, ⟨C⟩⟩

/-- **The game value is the infimum of certified bounds.** -/
theorem value_eq_sInf_cert (d : Desc) :
    value d = sInf {t | Nonempty (DualCert d.numMsgs (tester d) t)} := by
  refine (csInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_ ?_).symm
  · obtain ⟨t, -, -, hC⟩ := exists_dualCert_value d one_pos
    exact ⟨t, hC⟩
  · rintro t ⟨C⟩
    exact C.value_le
  · intro w hw
    obtain ⟨t, -, ht, hC⟩ := exists_dualCert_value d (half_pos (sub_pos.mpr hw))
    exact ⟨t, hC, by linarith⟩

end ShiQIP
