/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Sound
import QIP.Clean

/-!
# Q27 — completeness of the Bell test

If `d` has a prover accepting with probability exactly `1/2`, the honest prover of
`bellDesc d` runs it, stores message `m` (everything of `d`) in memory, and answers with the
Uhlmann partner of `B` (`bell_prob_eq_one`). It is accepted with certainty
(**`exists_accept_bell_one`**).

* `pureRun_relabel`, `accept_relabel`: relabelling prover memories by equivalences.
* Register layout: message `m` is `W + 2, …, 2W + 1`; message `m + 1` is the single wire `O'`.
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Relabelling memories -/

section Relabel

variable {e : Desc}

theorem turnVec_relabel (T T' : IsoStrategy (Reg e) (Reg e) e.numMsgs) (j : ℕ)
    (e0 : T'.M j ≃ T.M j) (e1 : T'.M (j + 1) ≃ T.M (j + 1))
    (hV : ∀ g a g' b, T'.V j (g, a) (g', b) = T.V j (g, e1 a) (g', e0 b))
    (v : Qubits e.totalWires × T.M j → ℂ) (v' : Qubits e.totalWires × T'.M j → ℂ)
    (hv : ∀ y b, v' (y, b) = v (y, e0 b)) (y : Qubits e.totalWires) (a : T'.M (j + 1)) :
    turnVec T' j v' (y, a) = turnVec T j v (y, e1 a) := by
  rw [PrefixData.turnVec_apply, PrefixData.turnVec_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fintype.sum_equiv e0 _ _ fun ν => by rw [hV, hv]

theorem pureRun_relabel (T T' : IsoStrategy (Reg e) (Reg e) e.numMsgs) (n : ℕ)
    (eM : ∀ k, k ≤ n → (T'.M k ≃ T.M k))
    (hinit : ∀ a, T'.init a = T.init (eM 0 (Nat.zero_le _) a))
    (hV : ∀ k (hk : k < n) g a g' b,
      T'.V k (g, a) (g', b) = T.V k (g, eM (k + 1) hk a) (g', eM k hk.le b)) :
    ∀ k (hk : k ≤ n) y a, pureRun T' k (y, a) = pureRun T k (y, eM k hk a)
  | 0, _, y, a => by
    rw [pureRun, pureRun, kron_one_mulVec_apply, kron_one_mulVec_apply]
    simp only [hinit]
  | k + 1, hk, y, a => by
    rw [pureRun, pureRun, kron_one_mulVec_apply, kron_one_mulVec_apply]
    congr 1
    funext y'
    exact turnVec_relabel T T' k (eM k (by omega)) (eM (k + 1) hk) (hV k (by omega)) _ _
      (fun y b => pureRun_relabel T T' n eM hinit hV k (by omega) y b) y' a

theorem accept_relabel (T T' : IsoStrategy (Reg e) (Reg e) e.numMsgs)
    (eM : ∀ k, k ≤ e.numMsgs → (T'.M k ≃ T.M k))
    (hinit : ∀ a, T'.init a = T.init (eM 0 (Nat.zero_le _) a))
    (hV : ∀ k (hk : k < e.numMsgs) g a g' b,
      T'.V k (g, a) (g', b) = T.V k (g, eM (k + 1) hk a) (g', eM k hk.le b)) :
    accept T'.toOp = accept T.toOp := by
  rw [accept_pureRun, accept_pureRun, accept_expect, accept_expect]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Fintype.sum_equiv (eM _ le_rfl) _ _ fun a => by
    rw [pureRun_relabel T T' _ eM hinit hV _ le_rfl]

end Relabel

/-! ## Register layout of the two new messages -/

variable {d : Desc}

theorem msgOffset_bell_m : (bellDesc d).msgOffset d.numMsgs = bellMsgOff d := by
  simp [Desc.msgOffset, bellDesc, Desc.numMsgs, bellMsgOff, Desc.totalWires]
  ring

theorem msgWidth_bell_m : (bellDesc d).msgWidth d.numMsgs = d.totalWires := by
  simp [Desc.msgWidth, bellDesc, Desc.numMsgs]

theorem msgOffset_bell_m1 : (bellDesc d).msgOffset (d.numMsgs + 1) = bellO d := by
  simp [Desc.msgOffset, bellDesc, Desc.numMsgs, bellO, Desc.totalWires, List.take_append]
  rw [List.take_of_length_le (by simp)]
  ring

theorem msgWidth_bell_m1 : (bellDesc d).msgWidth (d.numMsgs + 1) = 1 := by
  simp [Desc.msgWidth, bellDesc, Desc.numMsgs]

theorem inReg_bell_m (w : Fin (bellDesc d).totalWires) :
    inReg (bellDesc d) d.numMsgs w ↔ bellMsgOff d ≤ w ∧ (w : ℕ) < bellMsgOff d + d.totalWires := by
  unfold inReg; rw [msgOffset_bell_m, msgWidth_bell_m]

theorem inReg_bell_m1 (w : Fin (bellDesc d).totalWires) :
    inReg (bellDesc d) (d.numMsgs + 1) w ↔ w = wO d := by
  unfold inReg; rw [msgOffset_bell_m1, msgWidth_bell_m1]
  constructor
  · intro h; exact Fin.ext (by change (w : ℕ) = bellO d; omega)
  · rintro rfl; change bellO d ≤ bellO d ∧ bellO d < bellO d + 1; omega

theorem inReg_mw (x : Fin d.totalWires) : inReg (bellDesc d) d.numMsgs (mw d x) := by
  rw [inReg_bell_m, mw_val]; omega

/-- **Every wire outside message `m` other than `B` is `out'`, `O'` or a wire of `d`.** -/
theorem wire_cases (w : Fin (bellDesc d).totalWires) (hB : w ≠ wB d)
    (hm : ¬ inReg (bellDesc d) d.numMsgs w) :
    w = wOut d ∨ w = wO d ∨ ∃ x, w = sw d x := by
  rw [inReg_bell_m] at hm
  have hw : (w : ℕ) < 2 * d.totalWires + 3 := lt_of_lt_of_eq w.2 (totalWires_bellDesc d)
  have hp := priv_le_totalWires d
  have hB' : (w : ℕ) ≠ d.priv := fun h => hB (Fin.ext h)
  unfold bellMsgOff at hm
  by_cases h1 : (w : ℕ) < d.priv
  · exact Or.inr (Or.inr ⟨⟨w, by omega⟩, Fin.ext (by
      change (w : ℕ) = bellShift d w; unfold bellShift; rw [if_pos h1])⟩)
  by_cases h2 : (w : ℕ) = d.priv + 1
  · exact Or.inl (Fin.ext h2)
  by_cases h3 : (w : ℕ) < d.totalWires + 2
  · exact Or.inr (Or.inr ⟨⟨(w : ℕ) - 2, by omega⟩, Fin.ext (by
      change (w : ℕ) = bellShift d ((w : ℕ) - 2); unfold bellShift; rw [if_neg (by omega)]; omega)⟩)
  · exact Or.inr (Or.inl (Fin.ext (by change (w : ℕ) = bellO d; unfold bellO; omega)))

/-! ## The honest prover -/

section Honest

variable (hd : d.Valid) (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs)

variable (d) in
/-- The stored message `m` and the memory of `T₀` after turn `m - 1`. -/
abbrev StoreT (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs) : Type :=
  Reg (bellDesc d) d.numMsgs × T₀.M d.numMsgs

/-- The memories of the honest prover. -/
def hMem (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs) (k : ℕ) : Type :=
  if k ≤ d.numMsgs then T₀.M k else if k = d.numMsgs + 1 then StoreT d T₀ else Bool × StoreT d T₀

noncomputable instance hMem.fintype (k : ℕ) : Fintype (hMem T₀ k) := by
  unfold hMem; split_ifs <;> infer_instance

noncomputable instance hMem.decEq (k : ℕ) : DecidableEq (hMem T₀ k) := by
  unfold hMem; split_ifs <;> infer_instance

/-- `hMem k = T₀.M k` for `k ≤ m`. -/
def eM {k : ℕ} (hk : k ≤ d.numMsgs) : hMem T₀ k ≃ T₀.M k := Equiv.cast (by unfold hMem; rw [if_pos hk])

/-- `hMem (m + 1)` is the store. -/
def eA : hMem T₀ (d.numMsgs + 1) ≃ StoreT d T₀ :=
  Equiv.cast (by unfold hMem; rw [if_neg (by omega), if_pos rfl])

/-- `hMem (m + 2)` is a flag and the store. -/
def eB : hMem T₀ (d.numMsgs + 2) ≃ Bool × StoreT d T₀ :=
  Equiv.cast (by unfold hMem; rw [if_neg (by omega), if_neg (by omega)])

theorem iso_submatrix_equiv {α β α' β' : Type} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    [DecidableEq β] [DecidableEq β'] (V : Matrix α β ℂ) (hV : Vᴴ * V = 1) (e₁ : α' ≃ α)
    (e₂ : β' ≃ β) : (V.submatrix e₁ e₂)ᴴ * V.submatrix e₁ e₂ = 1 := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, hV]
  exact submatrix_one_equiv e₂

/-- Turns `k < m`: `T₀`, transported. -/
noncomputable def hVA {k : ℕ} (hk : k < d.numMsgs) :
    Matrix (Reg (bellDesc d) k × hMem T₀ (k + 1)) (Reg (bellDesc d) k × hMem T₀ k) ℂ :=
  (T₀.V k).submatrix (Prod.map ((bellPrefix d hd).τ k hk) (eM T₀ (k := k + 1) hk))
    (Prod.map ((bellPrefix d hd).τ k hk) (eM T₀ hk.le))

theorem hVA_iso {k : ℕ} (hk : k < d.numMsgs) : (hVA hd T₀ hk)ᴴ * hVA hd T₀ hk = 1 :=
  iso_submatrix_equiv _ (T₀.V_iso k hk) (((bellPrefix d hd).τ k hk).prodCongr (eM T₀ (k := k + 1) hk))
    (((bellPrefix d hd).τ k hk).prodCongr (eM T₀ hk.le))

/-- Turn `m`: move message `m` into memory, leaving `|0⟩`. -/
noncomputable def hVstore :
    Matrix (Reg (bellDesc d) d.numMsgs × hMem T₀ (d.numMsgs + 1))
      (Reg (bellDesc d) d.numMsgs × hMem T₀ d.numMsgs) ℂ :=
  Matrix.of fun p q => if p.1 = (fun _ => false) ∧ eA T₀ p.2 = (q.1, eM T₀ le_rfl q.2) then 1 else 0

theorem hVstore_iso : (hVstore T₀)ᴴ * hVstore T₀ = 1 := by
  ext ⟨g, μ⟩ ⟨g', μ'⟩
  simp only [mul_apply, conjTranspose_apply, hVstore, of_apply, one_apply]
  rw [Finset.sum_eq_single ((fun _ => false), (eA T₀).symm (g, eM T₀ le_rfl μ))]
  · simp only [Equiv.apply_symm_apply, true_and, if_true, star_one, one_mul, Prod.mk.injEq]
    by_cases h : g = g' ∧ μ = μ'
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg]
      intro hc
      apply h
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Equiv.apply_eq_iff_eq] at hc
      exact hc
  · rintro ⟨r, a⟩ _ hne
    rw [if_neg, star_zero, zero_mul]
    rintro ⟨h1, h2⟩
    apply hne
    change r = _ at h1; change eA T₀ a = _ at h2
    rw [h1, ← h2, Equiv.symm_apply_apply]
  · simp

/-- The value of message `m + 1` (the wire `O'`). -/
def oVal (r : Reg (bellDesc d) (d.numMsgs + 1)) : Bool := r ⟨wO d, (inReg_bell_m1 _).mpr rfl⟩

theorem reg_m1_ext {r r' : Reg (bellDesc d) (d.numMsgs + 1)} (h : oVal r = oVal r') : r = r' := by
  funext ⟨w, hw⟩
  have := (inReg_bell_m1 w).mp hw
  subst this
  exact h

/-- Turn `m + 1`: on `|0⟩` apply `V` (flag `0`); on `|1⟩` set the flag. -/
noncomputable def hWfin (V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ) :
    Matrix (Reg (bellDesc d) (d.numMsgs + 1) × hMem T₀ (d.numMsgs + 2))
      (Reg (bellDesc d) (d.numMsgs + 1) × hMem T₀ (d.numMsgs + 1)) ℂ :=
  Matrix.of fun p q =>
    if oVal q.1 = false then
      (if (eB T₀ p.2).1 = false then V (oVal p.1, (eA T₀).symm (eB T₀ p.2).2) q.2 else 0)
    else (if (eB T₀ p.2).1 = true ∧ oVal p.1 = false ∧ (eA T₀).symm (eB T₀ p.2).2 = q.2 then 1 else 0)

/-- `Reg (m + 1) ≃ Bool`. -/
def regBool : Reg (bellDesc d) (d.numMsgs + 1) ≃ Bool where
  toFun := oVal
  invFun b := fun _ => b
  left_inv _ := reg_m1_ext rfl
  right_inv _ := rfl

/-- The outputs of turn `m + 1`, as `O'`, the flag and a memory of turn `m + 1`. -/
def pe : Reg (bellDesc d) (d.numMsgs + 1) × hMem T₀ (d.numMsgs + 2) ≃
    Bool × (Bool × hMem T₀ (d.numMsgs + 1)) :=
  regBool.prodCongr ((eB T₀).trans ((Equiv.refl Bool).prodCongr (eA T₀).symm))

theorem oVal_pe_symm (o c : Bool) (x : hMem T₀ (d.numMsgs + 1)) :
    oVal ((pe T₀).symm (o, (c, x))).1 = o := rfl

theorem eB_pe_symm (o c : Bool) (x : hMem T₀ (d.numMsgs + 1)) :
    eB T₀ ((pe T₀).symm (o, (c, x))).2 = (c, eA T₀ x) := by
  simp [pe]

theorem hWfin_iso (V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ)
    (hV : Vᴴ * V = 1) : (hWfin T₀ V)ᴴ * hWfin T₀ V = 1 := by
  have hV' : ∀ a a', ∑ o, ∑ x, star (V (o, x) a) * V (o, x) a' = if a = a' then 1 else 0 := by
    intro a a'
    have := congrArg (fun M => M a a') hV
    simpa [mul_apply, Fintype.sum_prod_type, one_apply] using this
  ext ⟨r, a⟩ ⟨r', a'⟩
  rw [mul_apply, ← (pe T₀).symm.sum_comp]
  simp only [Fintype.sum_prod_type, conjTranspose_apply, hWfin, of_apply, oVal_pe_symm,
    eB_pe_symm, Equiv.symm_apply_apply, one_apply, Prod.mk.injEq]
  cases h : oVal r <;> cases h' : oVal r'
  · simp only [if_true, Fintype.sum_bool, Bool.true_eq_false, if_false, star_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    have := hV' a a'
    rw [Fintype.sum_bool] at this
    rw [zero_add, zero_add, this, reg_m1_ext (h.trans h'.symm)]
    simp
  · simp [Fintype.sum_bool]
    intro e; rw [e] at h; simp_all
  · simp [Fintype.sum_bool]
    intro e; rw [e] at h; simp_all
  · rw [reg_m1_ext (h.trans h'.symm)]
    simp [Fintype.sum_bool, eq_comm]

theorem isDensity_pureState_comp {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (v : α → ℂ) (h : IsDensity (pureState v)) (e : β ≃ α) : IsDensity (pureState (v ∘ e)) := by
  rw [← submatrix_pureState]
  exact ⟨h.posSemidef.submatrix e, by rw [trace_submatrix_equiv]; exact h.trace_eq_one⟩

/-- **The honest prover**, with final isometry built from `V`. -/
noncomputable def hT (V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ)
    (hV : Vᴴ * V = 1) : IsoStrategy (Reg (bellDesc d)) (Reg (bellDesc d)) (bellDesc d).numMsgs where
  M := hMem T₀
  init := T₀.init ∘ eM T₀ (Nat.zero_le _)
  init_density := isDensity_pureState_comp _ T₀.init_density _
  V k := if h : k < d.numMsgs then hVA hd T₀ h
    else if h2 : k = d.numMsgs then (by subst h2; exact hVstore T₀)
    else if h3 : k = d.numMsgs + 1 then (by subst h3; exact hWfin T₀ V)
    else 0
  V_iso k hk := by
    rw [numMsgs_bellDesc] at hk
    by_cases h : k < d.numMsgs
    · rw [dif_pos h]; exact hVA_iso hd T₀ h
    by_cases h2 : k = d.numMsgs
    · subst h2; rw [dif_neg h, dif_pos rfl]; exact hVstore_iso T₀
    have h3 : k = d.numMsgs + 1 := by omega
    subst h3
    rw [dif_neg h, dif_neg h2, dif_pos rfl]
    exact hWfin_iso T₀ V hV

variable {T₀} in
theorem hT_V_lt {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ}
    {hV : Vᴴ * V = 1} {k : ℕ} (h : k < d.numMsgs) : (hT hd T₀ V hV).V k = hVA hd T₀ h := by
  exact dif_pos h

variable {T₀} in
theorem hT_V_m {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ}
    {hV : Vᴴ * V = 1} : (hT hd T₀ V hV).V d.numMsgs = hVstore T₀ := by
  exact (dif_neg (lt_irrefl d.numMsgs)).trans (dif_pos rfl)

variable {T₀} in
theorem hT_V_m1 {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ}
    {hV : Vᴴ * V = 1} : (hT hd T₀ V hV).V (d.numMsgs + 1) = hWfin T₀ V := by
  exact ((dif_neg (show ¬ (d.numMsgs + 1 < d.numMsgs) by omega)).trans
    (dif_neg (show ¬ (d.numMsgs + 1 = d.numMsgs) by omega))).trans (dif_pos rfl)

/-- **The run up to turn `m` does not depend on the final isometry.** -/
theorem pureRun_hT_congr (V V' : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ)
    (hV : Vᴴ * V = 1) (hV' : V'ᴴ * V' = 1) (k : ℕ) (hk : k ≤ d.numMsgs + 1) (y : Qubits _)
    (a : hMem T₀ k) : pureRun (hT hd T₀ V hV) k (y, a) = pureRun (hT hd T₀ V' hV') k (y, a) :=
  pureRun_relabel (hT hd T₀ V' hV') (hT hd T₀ V hV) (d.numMsgs + 1) (fun _ _ => Equiv.refl _)
    (fun _ => rfl) (fun j hj g a g' b => by
      by_cases h : j < d.numMsgs
      · rw [hT_V_lt hd h, hT_V_lt hd h]; rfl
      · have : j = d.numMsgs := by omega
        subst this
        rw [hT_V_m hd, hT_V_m hd]; rfl) k hk y a

theorem restrict_hT_V (V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ)
    (hV : Vᴴ * V = 1) (k : ℕ) (hk : k < d.numMsgs) (g : Reg d k)
    (a : ((bellPrefix d hd).restrict (hT hd T₀ V hV)).M (k + 1)) (g' : Reg d k)
    (b : ((bellPrefix d hd).restrict (hT hd T₀ V hV)).M k) :
    ((bellPrefix d hd).restrict (hT hd T₀ V hV)).V k (g, a) (g', b) =
      T₀.V k (g, eM T₀ (k := k + 1) hk a) (g', eM T₀ hk.le b) := by
  have := (bellPrefix d hd).restrict_V (T := hT hd T₀ V hV) hk
    (((bellPrefix d hd).τ k hk).symm g) (((bellPrefix d hd).τ k hk).symm g') a b
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  rw [← this, hT_V_lt hd hk, hVA]
  show T₀.V k ((bellPrefix d hd).τ k hk (((bellPrefix d hd).τ k hk).symm g), _)
    ((bellPrefix d hd).τ k hk (((bellPrefix d hd).τ k hk).symm g'), _) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The restricted honest prover is `T₀`.** -/
theorem pBell_hT (V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ)
    (hV : Vᴴ * V = 1) : pBell d hd (hT hd T₀ V hV) = accept T₀.toOp := by
  rw [← accept_restrict hd]
  exact accept_relabel T₀ ((bellPrefix d hd).restrict (hT hd T₀ V hV)) (fun _ hk => eM T₀ hk)
    (fun _ => rfl) (restrict_hT_V hd T₀ V hV)

theorem pureRun_restrict_hT
    (V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ) (hV : Vᴴ * V = 1)
    (w : Qubits d.totalWires) (a : ((bellPrefix d hd).restrict (hT hd T₀ V hV)).M d.numMsgs) :
    pureRun ((bellPrefix d hd).restrict (hT hd T₀ V hV)) d.numMsgs (w, a) =
      pureRun T₀ d.numMsgs (w, eM T₀ le_rfl a) :=
  pureRun_relabel T₀ ((bellPrefix d hd).restrict (hT hd T₀ V hV)) d.numMsgs (fun _ hk => eM T₀ hk)
    (fun _ => rfl) (restrict_hT_V hd T₀ V hV) _ le_rfl w a

variable (d) in
/-- Every wire of a message to the prover reads `0` at the end of a run of `T₀`. -/
def CleanAt (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs) : Prop :=
  ∀ (j : ℕ) (w : Fin d.totalWires), toProverAt d j → inReg d j w →
    ∀ y μ, y w = true → pureRun T₀ d.numMsgs (y, μ) = 0

end Honest

/-! ## Support of the run after turn `m` -/

theorem wO_ne_sw (x : Fin d.totalWires) : wO d ≠ sw d x := fun h => by
  have h1 := congrArg Fin.val h
  change bellO d = bellShift d x at h1; have := x.2; unfold bellO bellShift at h1
  split_ifs at h1 <;> omega

theorem wO_ne_mw (x : Fin d.totalWires) : wO d ≠ mw d x := fun h => by
  have h1 := congrArg Fin.val h
  change bellO d = bellMsgOff d + x at h1; have := x.2; unfold bellO bellMsgOff at h1; omega

theorem σ_wO : σ d d.totalWires (wO d) = wO d := σ_fix _ _ wO_ne_sw wO_ne_mw

theorem wO_not_mem : wO d ∉ Set.range (bellEmb d) := fun ⟨x, hx⟩ => wO_ne_sw x hx.symm

theorem mw_not_mem (x : Fin d.totalWires) : mw d x ∉ Set.range (bellEmb d) :=
  fun ⟨i, hi⟩ => sw_ne_mw i x hi

theorem not_inReg_sw (x : Fin d.totalWires) : ¬ inReg (bellDesc d) d.numMsgs (sw d x) := by
  rw [inReg_bell_m, sw_val]; have := bellShift_lt_msgOff (d := d) x.2; omega

theorem not_inReg_wO : ¬ inReg (bellDesc d) d.numMsgs (wO d) := by
  rw [inReg_bell_m]; change ¬ (bellMsgOff d ≤ bellO d ∧ bellO d < _); unfold bellMsgOff bellO; omega

section Support

variable (hd : d.Valid) (T : IsoStrategy (Reg (bellDesc d)) (Reg (bellDesc d)) (bellDesc d).numMsgs)

include hd in
theorem pureRun_bell_sw (x : Fin d.totalWires) (hx : d.held d.numMsgs x = true)
    (y : Qubits (bellDesc d).totalWires)
    (μ : T.M d.numMsgs) (hy : y (sw d x) = true) : pureRun T d.numMsgs (y, μ) = 0 := by
  rw [pureRun_bell_apply hd]
  refine embV_eq_zero hd _ _ _ (mw d x) (mw_not_mem x) ?_
  rw [cnotFun, Function.update_of_ne (Ne.symm (wB_ne_mw x)), Function.comp_apply, σ_mw,
    if_pos ⟨x.2, hx⟩]
  exact hy

include hd in
theorem pureRun_bell_wO (y : Qubits (bellDesc d).totalWires) (μ : T.M d.numMsgs)
    (hy : y (wO d) = true) : pureRun T d.numMsgs (y, μ) = 0 := by
  rw [pureRun_bell_apply hd]
  refine embV_eq_zero hd _ _ _ (wO d) wO_not_mem ?_
  rw [cnotFun, Function.update_of_ne wO_ne_wB, Function.comp_apply, σ_wO]
  exact hy

theorem pureRun_bell_succ : pureRun T (d.numMsgs + 1) = turnVec T d.numMsgs (pureRun T d.numMsgs) := by
  change (blockMat (bellDesc d) (d.numMsgs + 1) ⊗ₖ (1 : Matrix (T.M (d.numMsgs + 1))
    (T.M (d.numMsgs + 1)) ℂ)) *ᵥ _ = _
  rw [blockMat_bell_mid, one_kronecker_one, one_mulVec]

include hd in
/-- **Acceptance of `bellDesc d` is the Bell probability after the last turn.** -/
theorem accept_eq_bellPr : accept T.toOp =
    bellPr (wB d) (wO d) (turnVec T (d.numMsgs + 1) (pureRun T (d.numMsgs + 1))) := by
  have hacc : accept T.toOp = (star (pureRun T (d.numMsgs + 2)) ⬝ᵥ
      (acceptEffect (bellDesc d) (T.M (d.numMsgs + 2)) *ᵥ pureRun T (d.numMsgs + 2))).re := by
    have key : ∀ k, k = (bellDesc d).numMsgs → accept T.toOp = (star (pureRun T k) ⬝ᵥ
        (acceptEffect (bellDesc d) (T.M k) *ᵥ pureRun T k)).re := by
      intro k hk; subst hk; exact accept_pureRun T
    exact key _ (numMsgs_bellDesc d).symm
  have hrun : ∀ y μ, pureRun T (d.numMsgs + 2) (y, μ) =
      runLayer (finalInstrs d) (fun y' => turnVec T (d.numMsgs + 1) (pureRun T (d.numMsgs + 1))
        (y', μ)) y := by
    intro y μ
    change ((blockMat (bellDesc d) (d.numMsgs + 2) ⊗ₖ (1 : Matrix (T.M (d.numMsgs + 2))
      (T.M (d.numMsgs + 2)) ℂ)) *ᵥ _) (y, μ) = _
    rw [kron_one_mulVec_apply, blockMat_bell_final, layerMat_mulVec]
  have hclean1 : ∀ y μ, y (wOut d) = true → pureRun T (d.numMsgs + 1) (y, μ) = 0 := by
    rw [pureRun_bell_succ]
    exact turnVec_vanish T _ (wOut d) (not_inReg_wOut _) _
      (fun y μ h => pureRun_bell_wOut hd T y μ h)
  rw [hacc, accept_expect_bell]
  simp only [hrun]
  exact acceptSum_final _ (turnVec_vanish T _ (wOut d) (not_inReg_wOut _) _ hclean1)

end Support

section HonestSupport

variable (hd : d.Valid) (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs)

theorem hT_V_m_apply {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ}
    {hV : Vᴴ * V = 1} (p q) : (hT hd T₀ V hV).V d.numMsgs p q = hVstore T₀ p q := by
  rw [hT_V_m hd]

theorem hT_vanish_reg {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ}
    {hV : Vᴴ * V = 1} (v : Qubits (bellDesc d).totalWires × (hT hd T₀ V hV).M d.numMsgs → ℂ)
    (y : Qubits (bellDesc d).totalWires) (a : (hT hd T₀ V hV).M (d.numMsgs + 1))
    (w : Fin (bellDesc d).totalWires) (hw : inReg (bellDesc d) d.numMsgs w) (hy : y w = true) :
    turnVec (hT hd T₀ V hV) d.numMsgs v (y, a) = 0 := by
  rw [PrefixData.turnVec_apply]
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun ν _ => ?_
  rw [hT_V_m_apply hd T₀]
  change (if ((wireSplitE _ _ y).2 = fun _ => false) ∧ eA T₀ a = (x, eM T₀ le_rfl ν) then (1 : ℂ)
    else 0) * _ = 0
  rw [if_neg, zero_mul]
  rintro ⟨h1, _⟩
  have := congrFun h1 ⟨w, hw⟩
  change y w = false at this
  rw [hy] at this
  exact Bool.noConfusion this

/-- A wire of `d` not held during block `m` belongs to a message sent to the prover. -/
theorem dead_of_not_held (x : Fin d.totalWires) (hx : d.held d.numMsgs x = false) :
    ∃ j, toProverAt d j ∧ inReg d j x := by
  have hp : d.priv ≤ (x : ℕ) := by
    by_contra h
    simp [Desc.held, show (x : ℕ) < d.priv by omega] at hx
  obtain ⟨i, h1, h2⟩ := exists_segment (segs d) x (by rw [segs_sum]; exact x.2)
  cases i with
  | zero => simp [psum, segs] at h2; omega
  | succ i =>
    have hreg : inReg d i x := by
      unfold inReg; rw [msgOffset_eq, msgWidth_eq]; exact ⟨h1, h2⟩
    refine ⟨i, ?_, hreg⟩
    have hi : i < d.numMsgs := by
      by_contra hc
      have : d.msgWidth i = 0 := by
        rw [msgWidth_eq]; simp [segs, List.getD_eq_getElem?_getD, Desc.numMsgs] at hc ⊢
        rw [List.getElem?_eq_none (by omega)]; rfl
      have := hreg.2; have := hreg.1; omega
    have hnot := hx
    rw [Bool.eq_false_iff, ne_eq, held_iff] at hnot
    unfold toProverAt
    cases hdir : (d.msgs.map Message.dir).getD i .toVerifier
    · exfalso
      exact hnot (Or.inr ⟨i, hreg, by rw [hdir]; simp [dirOk, hi]⟩)
    · rfl

theorem pureRun_bell_sw_dead (hclean : CleanAt d T₀)
    {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ} {hV : Vᴴ * V = 1}
    (x : Fin d.totalWires) (hx : d.held d.numMsgs x = false) (y : Qubits (bellDesc d).totalWires)
    (μ : (hT hd T₀ V hV).M d.numMsgs) (hy : y (sw d x) = true) :
    pureRun (hT hd T₀ V hV) d.numMsgs (y, μ) = 0 := by
  rw [pureRun_bell_apply hd]
  unfold PrefixData.embV
  split_ifs
  · rw [pureRun_restrict_hT hd T₀ V hV]
    obtain ⟨j, hpj, hjx⟩ := dead_of_not_held x hx
    refine hclean j x hpj hjx _ _ ?_
    rw [embSplit_fst]
    change cnotFun (sw d ⟨d.out, out_lt_W hd⟩) (wB d) (y ∘ σ d d.totalWires) (sw d x) = true
    rw [cnotFun, Function.update_of_ne (Ne.symm (wB_ne_sw x)), Function.comp_apply, σ_sw,
      if_neg (fun h => by rw [hx] at h; exact Bool.noConfusion h.2)]
    exact hy
  · rfl

/-- **After turn `m`, every wire other than `B` reads `0`.** -/
theorem hT_support (hclean : CleanAt d T₀)
    {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ}
    {hV : Vᴴ * V = 1} (y : Qubits (bellDesc d).totalWires) (a : (hT hd T₀ V hV).M (d.numMsgs + 1))
    (w : Fin (bellDesc d).totalWires) (hwB : w ≠ wB d) (hy : y w = true) :
    pureRun (hT hd T₀ V hV) (d.numMsgs + 1) (y, a) = 0 := by
  rw [pureRun_bell_succ]
  by_cases hm : inReg (bellDesc d) d.numMsgs w
  · exact hT_vanish_reg hd T₀ (V := V) (hV := hV) (pureRun (hT hd T₀ V hV) d.numMsgs) y a w hm hy
  · rcases wire_cases w hwB hm with rfl | rfl | ⟨x, rfl⟩
    · exact turnVec_vanish (hT hd T₀ V hV) d.numMsgs _ hm (pureRun (hT hd T₀ V hV) d.numMsgs)
        (fun y μ h => pureRun_bell_wOut hd (hT hd T₀ V hV) y μ h) y a hy
    · exact turnVec_vanish (hT hd T₀ V hV) d.numMsgs _ hm (pureRun (hT hd T₀ V hV) d.numMsgs)
        (fun y μ h => pureRun_bell_wO hd (hT hd T₀ V hV) y μ h) y a hy
    · by_cases hx : d.held d.numMsgs x = true
      · exact turnVec_vanish (hT hd T₀ V hV) d.numMsgs _ hm (pureRun (hT hd T₀ V hV) d.numMsgs)
          (fun y μ h => pureRun_bell_sw hd (hT hd T₀ V hV) x hx y μ h) y a hy
      · exact turnVec_vanish (hT hd T₀ V hV) d.numMsgs _ hm (pureRun (hT hd T₀ V hV) d.numMsgs)
          (fun y μ h => pureRun_bell_sw_dead hd T₀ hclean x (by simpa using hx) y μ h) y a hy

end HonestSupport

/-! ## The Uhlmann answer and certain acceptance -/

section Final

variable (hd : d.Valid) (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs)

/-- The honest prover with a placeholder final isometry. -/
noncomputable abbrev preT : IsoStrategy (Reg (bellDesc d)) (Reg (bellDesc d)) (bellDesc d).numMsgs :=
  hT hd T₀ (embFalse (hMem T₀ (d.numMsgs + 1))) embFalse_isometry

/-- The all-zero basis label. -/
def zeroQ (n : ℕ) : Qubits n := fun _ => false

/-- The state of `B` and the prover memory after turn `m`. -/
noncomputable def χB : Bool × hMem T₀ (d.numMsgs + 1) → ℂ := fun p =>
  pureRun (preT hd T₀) (d.numMsgs + 1) (Function.update (zeroQ _) (wB d) p.1, p.2)

theorem exists_ne_of_ne_zero {n : ℕ} {z : Qubits n} (h : z ≠ zeroQ n) : ∃ w, z w = true := by
  by_contra hc
  push Not at hc
  exact h (funext fun w => by simpa [zeroQ] using hc w)

theorem margB_preT (hclean : CleanAt d T₀) : margB (wB d) (pureRun (preT hd T₀) (d.numMsgs + 1)) =
    traceRight (pureState (χB hd T₀)) := by
  ext x x'
  rw [margB, of_apply, Finset.sum_eq_single ⟨zeroQ _, rfl⟩]
  · simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply, χB]
    rfl
  · rintro ⟨z, hz⟩ _ hne
    have hne' : z ≠ zeroQ _ := fun e => hne (Subtype.ext e)
    obtain ⟨w, hw⟩ := exists_ne_of_ne_zero hne'
    have hwB : w ≠ wB d := fun e => by rw [e, hz] at hw; exact Bool.noConfusion hw
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hT_support hd T₀ hclean _ a w hwB (by rw [Function.update_of_ne hwB]; exact hw), zero_mul]
  · simp

theorem isPurification_χB (hclean : CleanAt d T₀) (h : accept T₀.toOp = 1 / 2) :
    IsPurification (χB hd T₀) (diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ)) := by
  unfold IsPurification
  have hm : d.numMsgs < (bellDesc d).numMsgs := by rw [numMsgs_bellDesc]; omega
  rw [← margB_preT hd T₀ hclean, pureRun_bell_succ, margB_turnVec _ hm _ (not_inReg_wB _), margB_bell hd,
    pBell_hT, h]
  congr 1
  funext b
  cases b <;> norm_num

theorem nonempty_hMem (_h : accept T₀.toOp = 1 / 2) : Nonempty (hMem T₀ (d.numMsgs + 1)) := by
  have h1 := sum_norm_pureRun T₀ (le_refl d.numMsgs)
  by_contra hc
  rw [not_nonempty_iff] at hc
  have : IsEmpty (T₀.M d.numMsgs) := ⟨fun μ => hc.false ((eA T₀).symm (fun _ => false, μ))⟩
  simp at h1

theorem regSet_regBool (y : Qubits (bellDesc d).totalWires) (o : Bool) :
    PrefixData.regSet (bellDesc d) (d.numMsgs + 1) y (regBool.symm o) =
      Function.update y (wO d) o := by
  funext w
  rw [PrefixData.regSet_apply]
  by_cases hw : inReg (bellDesc d) (d.numMsgs + 1) w
  · have hw' := (inReg_bell_m1 w).mp hw
    subst hw'
    rw [dif_pos hw, Function.update_self]; rfl
  · rw [dif_neg hw, Function.update_of_ne (fun e => hw ((inReg_bell_m1 w).mpr e))]

theorem hT_V_m1_apply {V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ}
    {hV : Vᴴ * V = 1} (p q) : (hT hd T₀ V hV).V (d.numMsgs + 1) p q = hWfin T₀ V p q := by
  rw [hT_V_m1 hd]

/-- **The answer of the honest prover.** -/
theorem hT_last (hclean : CleanAt d T₀) (V : Matrix (Bool × hMem T₀ (d.numMsgs + 1)) (hMem T₀ (d.numMsgs + 1)) ℂ)
    (hV : Vᴴ * V = 1) (y : Qubits (bellDesc d).totalWires) (c : (hT hd T₀ V hV).M (d.numMsgs + 2)) :
    turnVec (hT hd T₀ V hV) (d.numMsgs + 1) (pureRun (hT hd T₀ V hV) (d.numMsgs + 1)) (y, c) =
      if (eB T₀ c).1 = false then ∑ a, V (y (wO d), (eA T₀).symm (eB T₀ c).2) a *
        pureRun (preT hd T₀) (d.numMsgs + 1) (Function.update y (wO d) false, a) else 0 := by
  rw [PrefixData.turnVec_apply, ← regBool.symm.sum_comp, Fintype.sum_bool]
  simp only [hT_V_m1_apply hd T₀, regSet_regBool]
  have h1 : ∀ ν, pureRun (hT hd T₀ V hV) (d.numMsgs + 1) (Function.update y (wO d) true, ν) = 0 :=
    fun ν => hT_support hd T₀ hclean _ ν (wO d) wO_ne_wB (Function.update_self _ _ _)
  simp only [h1, mul_zero, Finset.sum_const_zero, zero_add]
  trans ∑ x : (hT hd T₀ V hV).M (d.numMsgs + 1),
    (if (eB T₀ c).1 = false then V (y (wO d), (eA T₀).symm (eB T₀ c).2) x else 0) *
      pureRun (hT hd T₀ V hV) (d.numMsgs + 1) (Function.update y (wO d) false, x)
  · exact Finset.sum_congr rfl fun x _ => rfl
  split_ifs with hc
  · refine Finset.sum_congr rfl fun a _ => ?_
    exact congrArg _ (pureRun_hT_congr hd T₀ V _ hV embFalse_isometry _ le_rfl _ _)
  · simp

include hd in
/-- **Completeness of the Bell test**: from a prover of `d` accepted with probability `1/2`,
an isometric prover of `bellDesc d` accepted with certainty. -/
theorem exists_iso_accept_one (hclean : CleanAt d T₀) (h : accept T₀.toOp = 1 / 2) :
    ∃ T : IsoStrategy (Reg (bellDesc d)) (Reg (bellDesc d)) (bellDesc d).numMsgs,
      accept T.toOp = 1 := by
  have := nonempty_hMem T₀ h
  obtain ⟨V, hV, hprob⟩ := bell_prob_eq_one (χB hd T₀) (isPurification_χB hd T₀ hclean h)
  refine ⟨hT hd T₀ V hV, ?_⟩
  rw [trace_bell_pureState] at hprob
  rw [accept_eq_bellPr hd, ← hprob, bellPr, Finset.sum_eq_single ⟨zeroQ _, rfl, rfl⟩]
  · -- the all-zero label
    have hOB := (wO_ne_wB (d := d))
    have h0 : Function.update (zeroQ (bellDesc d).totalWires) (wO d) false =
        Function.update (zeroQ _) (wB d) false := by
      funext w; simp [Function.update_apply, zeroQ]
    have h11 : Function.update (Function.update (Function.update (zeroQ (bellDesc d).totalWires)
        (wO d) true) (wB d) true) (wO d) false = Function.update (zeroQ _) (wB d) true := by
      funext w
      simp only [Function.update_apply]
      split_ifs <;> simp_all [zeroQ]
    have hO : Function.update (Function.update (zeroQ (bellDesc d).totalWires) (wO d) true)
        (wB d) true (wO d) = true := by
      rw [Function.update_of_ne hOB, Function.update_self]
    simp only [hT_last hd T₀ hclean V hV, h0, h11, hO]
    refine (Fintype.sum_equiv ((eB T₀).trans ((Equiv.refl Bool).prodCongr (eA T₀).symm)) _
      (fun p => if p.1 = false then ‖assocVec (((1 : Matrix Bool Bool ℂ) ⊗ₖ V) *ᵥ χB hd T₀)
        ((false, false), p.2) + assocVec (((1 : Matrix Bool Bool ℂ) ⊗ₖ V) *ᵥ χB hd T₀)
          ((true, true), p.2)‖ ^ 2 / 2 else 0) fun c => ?_).trans ?_
    · simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst,
        Prod.map_snd, id_eq]
      split_ifs with hc
      · simp only [assocVec, one_kron_mulVec_apply]
        rfl
      · simp
    · rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp
  · -- labels with another wire set
    rintro ⟨z, hzB, hzO⟩ _ hne
    have hne' : z ≠ zeroQ _ := fun e => hne (Subtype.ext e)
    obtain ⟨w, hw⟩ := exists_ne_of_ne_zero hne'
    have hwB : w ≠ wB d := fun e => by rw [e, hzB] at hw; exact Bool.noConfusion hw
    have hwO : w ≠ wO d := fun e => by rw [e, hzO] at hw; exact Bool.noConfusion hw
    have hv : ∀ u : Qubits (bellDesc d).totalWires, u w = true → ∀ a,
        pureRun (preT hd T₀) (d.numMsgs + 1) (u, a) = 0 :=
      fun u hu a => hT_support hd T₀ hclean u a w hwB hu
    refine Finset.sum_eq_zero fun c _ => ?_
    simp only [hT_last hd T₀ hclean V hV]
    have e1 : ∀ a : hMem T₀ (d.numMsgs + 1), pureRun (preT hd T₀) (d.numMsgs + 1)
        (Function.update z (wO d) false, a) = 0 :=
      fun a => hv _ (by rw [Function.update_of_ne hwO]; exact hw) a
    have e2 : ∀ a : hMem T₀ (d.numMsgs + 1), pureRun (preT hd T₀) (d.numMsgs + 1)
        (Function.update (Function.update (Function.update z (wO d) true) (wB d) true) (wO d) false,
          a) = 0 :=
      fun a => hv _ (by rw [Function.update_of_ne hwO, Function.update_of_ne hwB,
        Function.update_of_ne hwO]; exact hw) a
    simp only [e1, e2, mul_zero, Finset.sum_const_zero, ite_self, add_zero, norm_zero]
    norm_num
  · simp

end Final

end ShiQIP
