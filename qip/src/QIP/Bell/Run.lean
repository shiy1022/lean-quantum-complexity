/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Copy
import QIP.PureRun
import QIP.Value

/-!
# Q27 — the Bell-test run after block `m`

* `turnVec_vanish`, **`margB_turnVec`**: a prover turn keeps a private wire at `0` and does not
  change its reduced state.
* `pureRun_bell_apply`: after block `m`, the global vector is `embV φ (cnot (y ∘ σ))`.
* **`margB_bell`**: the reduced state of `B` after block `m` is `diag(1 - p, p)`, where `p` is the
  acceptance probability of the restricted prover in `d`.
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Prover turns and private wires -/

theorem not_inReg_of_lt_priv (e : Desc) (j : ℕ) (w : Fin e.totalWires) (hw : (w : ℕ) < e.priv) :
    ¬ inReg e j w := fun h => by
  have : e.priv ≤ e.msgOffset j := by simp [Desc.msgOffset]
  exact absurd h.1 (by omega)

theorem turnSplit_symm_fst (e : Desc) (j : ℕ) (Mem : Type) (r : Rest e j) (g : Reg e j) (ν : Mem)
    (w : Fin e.totalWires) (hw : ¬ inReg e j w) :
    ((turnSplit e j Mem).symm (r, (g, ν))).1 w = r ⟨w, hw⟩ := by
  simp [turnSplit, Equiv.piEquivPiSubtypeProd, hw]

theorem one_kron_mulVec_apply {α β β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [Fintype β']
    (V : Matrix β β' ℂ) (u : α × β' → ℂ) (r : α) (q : β) :
    (((1 : Matrix α α ℂ) ⊗ₖ V) *ᵥ u) (r, q) = (V *ᵥ fun q' => u (r, q')) q := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

variable {e : Desc}

/-- **A prover turn keeps a wire outside its register at `0`.** -/
theorem turnVec_vanish (T : IsoStrategy (Reg e) (Reg e) e.numMsgs) (j : ℕ) (w : Fin e.totalWires)
    (hw : ¬ inReg e j w) (v : Qubits e.totalWires × T.M j → ℂ)
    (hv : ∀ y μ, y w = true → v (y, μ) = 0) :
    ∀ y μ, y w = true → turnVec T j v (y, μ) = 0 := by
  intro y μ hy
  change (((1 : Matrix (Rest e j) (Rest e j) ℂ) ⊗ₖ T.V j) *ᵥ (v ∘ (turnSplit e j (T.M j)).symm))
    (turnSplit e j (T.M (j + 1)) (y, μ)) = 0
  rw [show turnSplit e j (T.M (j + 1)) (y, μ) =
    ((turnSplit e j (T.M (j + 1)) (y, μ)).1, (turnSplit e j (T.M (j + 1)) (y, μ)).2) from rfl,
    one_kron_mulVec_apply]
  have h0 : (fun q' : Reg e j × T.M j => (v ∘ (turnSplit e j (T.M j)).symm)
      ((turnSplit e j (T.M (j + 1)) (y, μ)).1, q')) = 0 := by
    funext ⟨g, ν⟩
    exact hv _ _ ((turnSplit_symm_fst e j (T.M j) _ g ν w hw).trans hy)
  rw [h0, mulVec_zero]
  rfl

/-- **A prover turn does not change the reduced state of a wire outside its register.** -/
theorem margB_turnVec (T : IsoStrategy (Reg e) (Reg e) e.numMsgs) {j : ℕ} (hj : j < e.numMsgs)
    (b : Fin e.totalWires) (hb : ¬ inReg e j b) (v : Qubits e.totalWires × T.M j → ℂ) :
    margB b (turnVec T j v) = margB b v := by
  ext x x'
  have h1 := margB_eq_reduceTo b (turnVec T j v) (fun _ => x) (fun _ => x')
  have h2 := margB_eq_reduceTo b v (fun _ => x) (fun _ => x')
  rw [h1, h2, ← proverStep_pureState,
    reduceTo_proverStep T.toOp hj (wire1 b) (fun _ => hb)]

/-! ## Acceptance as a sum, for any description -/

theorem accept_expect (e : Desc) {M : Type} [Fintype M] [DecidableEq M]
    (v : Qubits e.totalWires × M → ℂ) :
    (star v ⬝ᵥ (acceptEffect e M *ᵥ v)).re =
      ∑ y, ∑ μ, if outBit e y then ‖v (y, μ)‖ ^ 2 else 0 := by
  have hmv : ∀ y μ, (acceptEffect e M *ᵥ v) (y, μ) = if outBit e y then v (y, μ) else 0 := by
    intro y μ
    rw [acceptEffect, kron_one_mulVec_apply, basisEffect, mulVec_diagonal]
    split_ifs <;> simp
  rw [dotProduct, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.star_apply, hmv]
  split_ifs
  · exact re_star_mul_self _
  · simp

/-- **A pure run is a unit vector.** -/
theorem sum_norm_pureRun (T : IsoStrategy (Reg e) (Reg e) e.numMsgs) {j : ℕ} (hj : j ≤ e.numMsgs) :
    ∑ y, ∑ μ, ‖pureRun T j (y, μ)‖ ^ 2 = 1 := by
  have h := (isDensity_stateAfterBlock T.toOp j hj).trace_eq_one
  rw [stateAfterBlock_pureRun] at h
  have h' := congrArg Complex.re h
  rw [trace, Complex.re_sum, Fintype.sum_prod_type] at h'
  simp only [diag_apply, pureState, vecMulVec_apply, Pi.star_apply] at h'
  rw [Complex.one_re] at h'
  rw [← h']
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_comm, re_star_mul_self]

/-! ## The state after block `m` -/

section AfterCopy

variable {d : Desc} (hd : d.Valid)
  (T : IsoStrategy (Reg (bellDesc d)) (Reg (bellDesc d)) (bellDesc d).numMsgs)

theorem wB_ne_sw (x : Fin d.totalWires) : wB d ≠ sw d x := fun h => by
  have h1 := congrArg Fin.val h
  change bellB d = bellShift d x at h1; unfold bellB bellShift at h1
  split_ifs at h1 <;> omega

theorem wOut_ne_sw (x : Fin d.totalWires) : wOut d ≠ sw d x := fun h => by
  have h1 := congrArg Fin.val h
  change bellOut d = bellShift d x at h1; unfold bellOut bellShift at h1
  split_ifs at h1 <;> omega

theorem wB_ne_mw (x : Fin d.totalWires) : wB d ≠ mw d x := fun h => by
  have h1 := congrArg Fin.val h; have := priv_le_totalWires d
  change bellB d = bellMsgOff d + x at h1; unfold bellB bellMsgOff at h1; omega

theorem wOut_ne_mw (x : Fin d.totalWires) : wOut d ≠ mw d x := fun h => by
  have h1 := congrArg Fin.val h; have := priv_le_totalWires d
  change bellOut d = bellMsgOff d + x at h1; unfold bellOut bellMsgOff at h1; omega

theorem σ_wB : σ d d.totalWires (wB d) = wB d := σ_fix _ _ wB_ne_sw wB_ne_mw
theorem σ_wOut : σ d d.totalWires (wOut d) = wOut d := σ_fix _ _ wOut_ne_sw wOut_ne_mw

theorem wB_not_mem : wB d ∉ Set.range (bellEmb d) := fun ⟨x, hx⟩ => wB_ne_sw x hx.symm
theorem wOut_not_mem : wOut d ∉ Set.range (bellEmb d) := fun ⟨x, hx⟩ => wOut_ne_sw x hx.symm

/-- **After block `m`.** -/
theorem pureRun_bell_apply (y : Qubits (bellDesc d).totalWires) (μ : T.M d.numMsgs) :
    pureRun T d.numMsgs (y, μ) = (bellPrefix d hd).embV
      (pureRun ((bellPrefix d hd).restrict T) d.numMsgs)
        (cnotFun (sw d ⟨d.out, out_lt_W hd⟩) (wB d) (y ∘ σ d d.totalWires), μ) := by
  rw [(bellPrefix d hd).pureRun_prefix_last T, kron_one_mulVec_apply]
  exact bellG_mulVec hd _ y

theorem embV_eq_zero {M : Type} (v : Qubits d.totalWires × M → ℂ) (u : Qubits (bellDesc d).totalWires)
    (μ : M) (w : Fin (bellDesc d).totalWires) (hw : w ∉ Set.range (bellEmb d)) (hu : u w = true) :
    (bellPrefix d hd).embV v (u, μ) = 0 := by
  unfold PrefixData.embV
  rw [if_neg]
  intro h
  have := congrFun h ⟨w, hw⟩
  rw [embSplit_snd] at this
  change u w = false at this
  rw [hu] at this
  exact Bool.noConfusion this

include hd in
/-- **The new output is still `0` after block `m`.** -/
theorem pureRun_bell_wOut (y : Qubits (bellDesc d).totalWires) (μ : T.M d.numMsgs)
    (hy : y (wOut d) = true) : pureRun T d.numMsgs (y, μ) = 0 := by
  rw [pureRun_bell_apply hd]
  refine embV_eq_zero hd _ _ _ (wOut d) wOut_not_mem ?_
  rw [cnotFun, Function.update_of_ne (Ne.symm wB_ne_wOut), Function.comp_apply, σ_wOut]
  exact hy

theorem mul_star_eq_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem σ_symm_mw_out (hd : d.Valid) :
    (σ d d.totalWires).symm (mw d ⟨d.out, out_lt_W hd⟩) = sw d ⟨d.out, out_lt_W hd⟩ := by
  rw [Equiv.symm_apply_eq, σ_sw_out hd]

theorem σ_symm_wB : (σ d d.totalWires).symm (wB d) = wB d := by
  rw [Equiv.symm_apply_eq, σ_wB]

theorem pureRun_bell_update (z : Qubits (bellDesc d).totalWires) (hz : z (wB d) = false) (x : Bool)
    (μ : T.M d.numMsgs) :
    pureRun T d.numMsgs (Function.update z (wB d) x, μ) =
      if x = z (mw d ⟨d.out, out_lt_W hd⟩) then
        (bellPrefix d hd).embV (pureRun ((bellPrefix d hd).restrict T) d.numMsgs)
          (z ∘ σ d d.totalWires, μ) else 0 := by
  rw [pureRun_bell_apply hd]
  have hmB : mw d ⟨d.out, out_lt_W hd⟩ ≠ wB d := Ne.symm (wB_ne_mw _)
  have hc1 : cnotFun (sw d ⟨d.out, out_lt_W hd⟩) (wB d)
      (Function.update z (wB d) x ∘ σ d d.totalWires) (wB d) = xor x (z (mw d ⟨d.out, out_lt_W hd⟩)) := by
    rw [cnotFun, Function.update_self, Function.comp_apply, Function.comp_apply, σ_wB,
      σ_sw_out hd, Function.update_self, Function.update_of_ne hmB]
  split_ifs with hx
  · congr 2
    funext w
    by_cases hw : w = wB d
    · subst hw
      rw [hc1, hx, Bool.xor_self, Function.comp_apply, σ_wB, hz]
    · rw [cnotFun, Function.update_of_ne hw, Function.comp_apply, Function.comp_apply,
        Function.update_of_ne]
      intro h
      apply hw
      rw [← σ_wB (d := d)] at h
      exact (σ d d.totalWires).injective h
  · refine embV_eq_zero hd _ _ _ (wB d) wB_not_mem ?_
    rw [hc1]
    cases x <;> cases h : z (mw d ⟨d.out, out_lt_W hd⟩) <;> simp_all

variable (d) in
/-- The acceptance probability of the restricted prover, as a sum. -/
noncomputable def pBell : ℝ :=
  ∑ a, ∑ μ, if a ⟨d.out, out_lt_W hd⟩ = true then
    ‖pureRun ((bellPrefix d hd).restrict T) d.numMsgs (a, μ)‖ ^ 2 else 0

theorem embSplit_symm_emb {M' : ℕ} {α : Type} [Fintype α] (f : α ↪ Fin M') (a : α → Bool)
    (r : Outside f → Bool) (i : α) : (embSplit f).symm (a, r) (f i) = a i := by
  have := embSplit_fst f ((embSplit f).symm (a, r)) i
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

theorem embSplit_symm_out {M' : ℕ} {α : Type} [Fintype α] (f : α ↪ Fin M') (a : α → Bool)
    (r : Outside f → Bool) (w : Outside f) : (embSplit f).symm (a, r) w.1 = r w := by
  have := embSplit_snd f ((embSplit f).symm (a, r)) w
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- **The reduced state of `B` after block `m` is `diag(1 - p, p)`.** -/
theorem margB_bell : margB (wB d) (pureRun T d.numMsgs) =
    diagonal fun b => (((if b then pBell d hd T else 1 - pBell d hd T) : ℝ) : ℂ) := by
  set φ := pureRun ((bellPrefix d hd).restrict T) d.numMsgs with hφ
  set S : Qubits d.totalWires → ℝ := fun a => ∑ μ, ‖φ (a, μ)‖ ^ 2
  have hS1 : ∑ a, S a = 1 := sum_norm_pureRun _ le_rfl
  -- the diagonal, as a real sum over `d`'s basis labels
  have hdiag : ∀ x : Bool, margB (wB d) (pureRun T d.numMsgs) x x =
      ((∑ a, if a ⟨d.out, out_lt_W hd⟩ = x then S a else 0 : ℝ) : ℂ) := by
    intro x
    rw [margB, of_apply]
    have h1 : ∀ z : Z0 (wB d), (∑ μ, pureRun T d.numMsgs (Function.update z.1 (wB d) x, μ) *
        star (pureRun T d.numMsgs (Function.update z.1 (wB d) x, μ))) =
        ((if z.1 (mw d ⟨d.out, out_lt_W hd⟩) = x then
          ∑ μ, ‖(bellPrefix d hd).embV φ (z.1 ∘ σ d d.totalWires, μ)‖ ^ 2 else 0 : ℝ) : ℂ) := by
      intro z
      simp only [pureRun_bell_update hd T z.1 z.2]
      by_cases hx : z.1 (mw d ⟨d.out, out_lt_W hd⟩) = x
      · simp only [if_pos hx.symm, if_pos hx]
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun μ _ => mul_star_eq_norm_sq _
      · simp only [if_neg (fun h : x = _ => hx h.symm), if_neg hx]
        simp
    simp only [h1]
    rw [← Complex.ofReal_sum]
    congr 1
    -- change variables `u = z ∘ σ`, then split `u` along the embedding
    let e : Z0 (wB d) ≃ Z0 (wB d) :=
      { toFun := fun z => ⟨z.1 ∘ σ d d.totalWires, by
          rw [Function.comp_apply, σ_wB]; exact z.2⟩
        invFun := fun u => ⟨u.1 ∘ (σ d d.totalWires).symm, by
          rw [Function.comp_apply, σ_symm_wB]; exact u.2⟩
        left_inv := fun z => Subtype.ext (funext fun w => by simp)
        right_inv := fun u => Subtype.ext (funext fun w => by simp) }
    rw [← e.symm.sum_comp]
    have h2 : ∀ u : Z0 (wB d), (e.symm u).1 (mw d ⟨d.out, out_lt_W hd⟩) = u.1 (sw d ⟨d.out, out_lt_W hd⟩) := by
      intro u
      change u.1 ((σ d d.totalWires).symm (mw d ⟨d.out, out_lt_W hd⟩)) = _
      rw [σ_symm_mw_out hd]
    have h3 : ∀ u : Z0 (wB d), (e.symm u).1 ∘ σ d d.totalWires = u.1 := by
      intro u; funext w; simp [e]
    simp only [h2, h3]
    rw [← Finset.sum_subtype (Finset.univ.filter fun u : Qubits _ => u (wB d) = false) (by simp)
      (fun u : Qubits _ => if u (sw d ⟨d.out, out_lt_W hd⟩) = x then
        ∑ μ, ‖(bellPrefix d hd).embV φ (u, μ)‖ ^ 2 else 0), Finset.sum_filter,
      ← (embSplit (bellEmb d)).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (fun _ => false)]
    · rw [show (wB d) = (⟨wB d, wB_not_mem⟩ : Outside (bellEmb d)).1 from rfl, embSplit_symm_out,
        if_pos rfl, show sw d ⟨d.out, out_lt_W hd⟩ = bellEmb d ⟨d.out, out_lt_W hd⟩ from rfl, embSplit_symm_emb]
      split_ifs
      · refine Finset.sum_congr rfl fun μ _ => ?_
        simp only [PrefixData.embV]
        rw [show (bellPrefix d hd).ε = bellEmb d from rfl, Equiv.apply_symm_apply, if_pos rfl]
      · rfl
    · intro r _ hr
      split_ifs
      · refine Finset.sum_eq_zero fun μ _ => ?_
        simp only [PrefixData.embV]
        rw [show (bellPrefix d hd).ε = bellEmb d from rfl, Equiv.apply_symm_apply, if_neg hr,
          norm_zero]
        norm_num
      · rfl
      · rfl
    · simp
  ext x x'
  by_cases hxx : x = x'
  · subst hxx
    rw [hdiag, diagonal_apply_eq]
    congr 1
    cases x
    · simp only [Bool.false_eq_true, if_false]
      rw [← hS1, eq_sub_iff_add_eq, pBell, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      change _ + ∑ μ, _ = S a
      by_cases ha : a ⟨d.out, out_lt_W hd⟩ = true
      · rw [if_neg (by simp [ha]), zero_add, Finset.sum_congr rfl fun μ _ => if_pos ha]
      · rw [if_pos (by simpa using ha), Finset.sum_congr rfl fun μ _ => if_neg ha,
          Finset.sum_const_zero, add_zero]
    · simp only [if_true, pBell]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · rfl
      · simp
  · rw [diagonal_apply_ne _ hxx, margB, of_apply]
    refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun μ _ => ?_
    rw [pureRun_bell_update hd T z.1 z.2, pureRun_bell_update hd T z.1 z.2]
    split_ifs with h1 h2
    · exact absurd (h1.trans h2.symm) hxx
    · simp
    · simp
    · simp

end AfterCopy

end ShiQIP
