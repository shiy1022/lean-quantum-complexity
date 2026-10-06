/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Tester

/-!
# Q21 — compactness and the attained game value

For a verifier description `d` with `m = d.numMsgs` messages:

* `feasible d`: the causal strategy families `(Q k)_{k ≤ m}`, as a subset of the finite product
  of matrix spaces `Fam d = ∀ k : Fin (m + 1), Matrix (Hist k) (Hist k) ℂ`;
* `isClosed_feasible`, `feasible_subset_box`: it is closed and bounded (entries of a PSD
  matrix are bounded by its trace, `norm_apply_le_trace`, and traces of strategy operators are
  fixed); so `isCompact_feasible`;
* the pairing with the tester is continuous, so it attains its maximum on `feasible d`;
* **`exists_optimal_prover`**: some prover `Pstar` (constructed by the realization theorem, with
  memory `Hist k`) satisfies `accept P ≤ accept Pstar` for **every** prover `P`;
* `value d = sSup {accept P}` is attained (`value_attained`), lies in `[0, 1]`, and reconciles
  the existential/universal class conditions with value inequalities (`le_value_iff`,
  `value_le_iff`, `exists_accept_eq_one_of_value_eq_one`).

No bound on the prover's memory is assumed; the bounded-memory optimizer is *proved* to exist.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Matrix facts -/

theorem norm_apply_le_trace {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (i j : n) : ‖M i j‖ ≤ (trace M).re := by
  obtain ⟨B, rfl⟩ := PSD_exists_eq_mul_conjTranspose hM
  have hdiag : ∀ a, ((B * Bᴴ) a a).re = ∑ k, ‖B a k‖ ^ 2 := by
    intro a
    simp only [mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hentry : ‖(B * Bᴴ) i j‖ ≤ ((B * Bᴴ) i i).re / 2 + ((B * Bᴴ) j j).re / 2 := by
    rw [hdiag, hdiag, mul_apply]
    calc ‖∑ k, B i k * Bᴴ k j‖ ≤ ∑ k, ‖B i k * Bᴴ k j‖ := norm_sum_le _ _
      _ = ∑ k, ‖B i k‖ * ‖B j k‖ := by
          simp [conjTranspose_apply]
      _ ≤ ∑ k, (‖B i k‖ ^ 2 / 2 + ‖B j k‖ ^ 2 / 2) :=
          Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (‖B i k‖ - ‖B j k‖)]
      _ = (∑ k, ‖B i k‖ ^ 2) / 2 + (∑ k, ‖B j k‖ ^ 2) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
  have hpsd := posSemidef_self_mul_conjTranspose B
  have hnn : ∀ a, 0 ≤ ((B * Bᴴ) a a).re := fun a => (Complex.nonneg_iff.mp (hpsd.diag_nonneg)).1
  have htr : (trace (B * Bᴴ)).re = ∑ a, ((B * Bᴴ) a a).re := by
    simp [trace, Complex.re_sum]
  have hle : ∀ a, ((B * Bᴴ) a a).re ≤ (trace (B * Bᴴ)).re := fun a => by
    rw [htr]
    exact Finset.single_le_sum (fun b _ => hnn b) (Finset.mem_univ a)
  have := hle i; have := hle j
  linarith

theorem isClosed_nonneg_complex : IsClosed {z : ℂ | 0 ≤ z} := by
  have : {z : ℂ | 0 ≤ z} = {z | 0 ≤ z.re} ∩ {z | z.im = 0} := by
    ext z; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Complex.nonneg_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  rw [this]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

theorem isClosed_posSemidef {n : Type} [Fintype n] :
    IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
  have : {M : Matrix n n ℂ | M.PosSemidef} =
      {M | Mᴴ = M} ∩ ⋂ x : n → ℂ, {M | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => ?_)
  refine isClosed_nonneg_complex.preimage ?_
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem i j).mul continuous_const)

theorem continuous_traceRight {α α' β : Type} [Fintype β] :
    Continuous (traceRight : Matrix (α × β) (α' × β) ℂ → Matrix α α' ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [traceRight_apply]
  exact continuous_finsetSum _ fun i _ => continuous_id.matrix_elem (a, i) (b, i)

theorem continuous_kronecker_one {α β : Type} [DecidableEq β] :
    Continuous (fun M : Matrix α α ℂ => M ⊗ₖ (1 : Matrix β β ℂ)) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [kroneckerMap_apply]
  exact (continuous_id.matrix_elem p.1 q.1).mul continuous_const

/-! ## The feasible set of strategy families -/

variable (d : Desc)

/-- Histories of `d`. -/
abbrev HistD (k : ℕ) : Type := Hist (Reg d) (Reg d) k

/-- Strategy families up to turn `m`. -/
abbrev Fam : Type := ∀ k : Fin (d.numMsgs + 1), Matrix (HistD d k) (HistD d k) ℂ

/-- Extend a family by `0` beyond turn `m`. -/
def extendFam (F : Fam d) : ∀ k : ℕ, Matrix (HistD d k) (HistD d k) ℂ :=
  fun k => if h : k < d.numMsgs + 1 then F ⟨k, h⟩ else 0

theorem extendFam_apply (F : Fam d) {k : ℕ} (h : k < d.numMsgs + 1) :
    extendFam d F k = F ⟨k, h⟩ := dif_pos h

/-- The causal strategy families. -/
def feasible : Set (Fam d) := {F | IsStrategy d.numMsgs (extendFam d F)}

/-- The family of a prover. -/
noncomputable def proverFam (P : Prover d) : Fam d := fun k => stratOp P k

theorem isStrategy_congr {r : ℕ} {Q Q' : ∀ k, Matrix (HistD d k) (HistD d k) ℂ}
    (h : ∀ k ≤ r, Q k = Q' k) (hQ : IsStrategy r Q) : IsStrategy r Q' where
  zero := by rw [← h 0 (Nat.zero_le _)]; exact hQ.zero
  posSemidef k hk := by rw [← h k hk]; exact hQ.posSemidef k hk
  causal k hk := by rw [← h k (by omega), ← h (k + 1) hk]; exact hQ.causal k hk

theorem proverFam_mem (P : Prover d) : proverFam d P ∈ feasible d :=
  isStrategy_congr d (fun k hk => by rw [extendFam_apply d _ (by omega)]; rfl)
    (opStrategy_isStrategy P)

theorem isClosed_feasible : IsClosed (feasible d) := by
  have e : feasible d = {F : Fam d | F 0 = 1} ∩
      (⋂ k : Fin (d.numMsgs + 1), {F : Fam d | (F k).PosSemidef}) ∩
      ⋂ k : Fin d.numMsgs, {F : Fam d | Causal (k : ℕ) (F k.castSucc) (F k.succ)} := by
    ext F
    simp only [feasible, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      refine ⟨⟨?_, fun k => ?_⟩, fun k => ?_⟩
      · have := h.zero; rwa [extendFam_apply d F (Nat.succ_pos _)] at this
      · have := h.posSemidef k (by omega); rwa [extendFam_apply d F k.isLt] at this
      · have := h.causal k k.isLt
        rwa [extendFam_apply d F (by omega), extendFam_apply d F (by omega)] at this
    · rintro ⟨⟨h0, hp⟩, hc⟩
      refine ⟨?_, fun k hk => ?_, fun k hk => ?_⟩
      · rw [extendFam_apply d F (Nat.succ_pos _)]; exact h0
      · rw [extendFam_apply d F (by omega)]; exact hp ⟨k, by omega⟩
      · rw [extendFam_apply d F (by omega), extendFam_apply d F (by omega)]
        exact hc ⟨k, hk⟩
  rw [e]
  refine ((isClosed_eq (continuous_apply _) continuous_const).inter
    (isClosed_iInter fun k => IsClosed.preimage (f := fun F : Fam d => F k)
      (continuous_apply k) (isClosed_posSemidef (n := HistD d k)))).inter
    (isClosed_iInter fun k => ?_)
  unfold Causal
  exact isClosed_eq (continuous_traceRight.comp (continuous_apply _))
    (continuous_kronecker_one.comp (continuous_apply _))

/-- The trace of turn `k` of a strategy, as a real bound. -/
noncomputable def traceBound (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (Fintype.card (Reg d i) : ℝ)

/-- Matrices with entries bounded by `C`. -/
def entryBox {n : Type} (C : ℝ) : Set (Matrix n n ℂ) := {M | ∀ i j, ‖M i j‖ ≤ C}

theorem isCompact_entryBox {n : Type} [Fintype n] (C : ℝ) :
    IsCompact (entryBox (n := n) C) := by
  have h : IsCompact (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : entryBox (n := n) C = Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) C := by
    ext M
    constructor
    · intro h i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using h i j
    · intro h i j
      have := h i (Set.mem_univ _) j (Set.mem_univ _)
      simpa [Metric.mem_closedBall, dist_zero_right] using this
  rw [e]; exact h

/-- The compact box containing all feasible families. -/
def box : Set (Fam d) := Set.pi Set.univ fun k => entryBox (traceBound d k)

theorem isCompact_box : IsCompact (box d) :=
  isCompact_univ_pi fun _ => isCompact_entryBox _

theorem feasible_subset_box : feasible d ⊆ box d := by
  intro F hF
  simp only [box, Set.mem_pi, Set.mem_univ, true_implies, entryBox, Set.mem_ofPred_eq]
  intro k i j
  have hp := hF.posSemidef k (by omega)
  have ht := hF.trace_eq k (by omega)
  rw [extendFam_apply d F k.isLt] at hp ht
  have := norm_apply_le_trace hp i j
  rw [ht, ← Nat.cast_prod, Complex.natCast_re] at this
  rwa [traceBound, ← Nat.cast_prod]

theorem isCompact_feasible : IsCompact (feasible d) :=
  (isCompact_box d).of_isClosed_subset (isClosed_feasible d) (feasible_subset_box d)

/-! ## The attained value -/

/-- The pairing of a family with the tester. -/
noncomputable def pairing (F : Fam d) : ℝ :=
  (trace (tester d * F ⟨d.numMsgs, Nat.lt_succ_self _⟩)).re

theorem continuous_pairing : Continuous (pairing d) :=
  Complex.continuous_re.comp (continuous_const.matrix_mul (continuous_apply _)).matrix_trace

theorem accept_eq_pairing_fam (P : Prover d) : accept P = pairing d (proverFam d P) :=
  accept_eq_pairing P

/-- A prover with no memory that leaves every register unchanged. -/
def trivialProver : Prover d where
  M _ := Unit
  init := 1
  init_density := (isDensity_unique_iff _).mpr rfl
  act _ := LinearMap.id
  act_channel _ _ := isChannel_id

/-- **An optimal prover exists.** -/
theorem exists_optimal_prover : ∃ Pstar : Prover d, ∀ P : Prover d, accept P ≤ accept Pstar := by
  obtain ⟨F, hF, hmax⟩ := (isCompact_feasible d).exists_isMaxOn
    ⟨_, proverFam_mem d (trivialProver d)⟩ (continuous_pairing d).continuousOn
  obtain ⟨S, -, hS⟩ := exists_opStrategy_of_isStrategy hF
  refine ⟨S, fun P => ?_⟩
  have hSF : accept S = pairing d F := by
    rw [accept_eq_pairing, pairing, hS _ le_rfl, extendFam_apply d F (Nat.lt_succ_self _)]
  rw [hSF, accept_eq_pairing_fam]
  exact hmax (proverFam_mem d P)

/-- The value of the verifier: the supremum of acceptance over all provers. -/
noncomputable def value : ℝ := sSup (Set.range (accept (d := d)))

theorem bddAbove_accept : BddAbove (Set.range (accept (d := d))) :=
  ⟨1, by rintro _ ⟨P, rfl⟩; exact (accept_mem_Icc P).2⟩

/-- **The value is attained.** -/
theorem value_attained : ∃ Pstar : Prover d, accept Pstar = value d := by
  obtain ⟨Pstar, h⟩ := exists_optimal_prover d
  refine ⟨Pstar, le_antisymm (le_csSup (bddAbove_accept d) ⟨Pstar, rfl⟩) ?_⟩
  exact csSup_le ⟨_, ⟨Pstar, rfl⟩⟩ (by rintro _ ⟨P, rfl⟩; exact h P)

theorem accept_le_value (P : Prover d) : accept P ≤ value d :=
  le_csSup (bddAbove_accept d) ⟨P, rfl⟩

theorem value_mem_Icc : value d ∈ Set.Icc 0 1 := by
  obtain ⟨Pstar, h⟩ := value_attained d
  rw [← h]; exact accept_mem_Icc Pstar

/-- Completeness as a value inequality. -/
theorem le_value_iff (c : ℝ) : (∃ P : Prover d, c ≤ accept P) ↔ c ≤ value d := by
  constructor
  · rintro ⟨P, hP⟩; exact hP.trans (accept_le_value d P)
  · intro h; obtain ⟨Pstar, hP⟩ := value_attained d; exact ⟨Pstar, hP ▸ h⟩

/-- Soundness as a value inequality. -/
theorem value_le_iff (s : ℝ) : (∀ P : Prover d, accept P ≤ s) ↔ value d ≤ s := by
  constructor
  · intro h; obtain ⟨Pstar, hP⟩ := value_attained d; rw [← hP]; exact h Pstar
  · intro h P; exact (accept_le_value d P).trans h

/-- **Value one yields a perfect prover.** -/
theorem exists_accept_eq_one_of_value_eq_one (h : value d = 1) : ∃ P : Prover d, accept P = 1 := by
  obtain ⟨Pstar, hP⟩ := value_attained d
  exact ⟨Pstar, hP.trans h⟩

end ShiQIP
