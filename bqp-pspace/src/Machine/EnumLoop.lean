/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

One iteration of the enumerator loop (plan tasks S10, S12, S13).
-/
import Machine.EnumInit
import Definitions.Def_PvsNP

set_option autoImplicit false

/-!
# One witness per iteration

From the loop head `prepA` with `inp = x`, `wit = w`, `cnt = c` (other stacks empty), one
iteration

1. writes `encodePair (x, w)` (through the input alphabet equivalence) onto the checker input
   stack, restoring `wit` and `inp`;
2. runs the embedded checker to its halt, i.e. to `ans`;
3. pops the checker answer, leaving every checker stack empty (a clean restart state);
4. increments `cnt` iff the checker accepted;
5. increments `wit`, returning to `prepA`, or to `finA` on overflow.

The peak is the checker's own peak plus the registers, and the preparation peak
`2 (n + |w|) + |c|`.
-/

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

/-- Close `join chk R.get = join chk' R'.get` goals. -/
macro "join_eq" : tactic =>
  `(tactic| (congr 1 <;> first | (funext e; cases e <;> rfl) | rfl | simp [nochk]))

theorem initList_stk_eq (tm : FinTM2) (L : List (tm.Γ tm.k₀)) :
    (initList tm L).stk = Function.update (nochk tm) tm.k₀ L := by
  funext j
  by_cases h : j = tm.k₀
  · subst h; rw [Function.update_self, initList_stk_self]
  · rw [Function.update_of_ne h, initList_stk_ne tm L j h]; rfl

theorem haltList_pop (tm : FinTM2) (a : tm.Γ tm.k₁) :
    Function.update (haltList tm [a]).stk tm.k₁ [] = nochk tm := by
  funext j
  by_cases h : j = tm.k₁
  · subst h; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne h, haltList_stk_ne tm [a] j h]; rfl

variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ (Bool ⊕ Bool)) (eout : tm.Γ tm.k₁ ≃ Bool) (k : ℕ)

local notation "M" => prog tm ein eout k
local notation "run" => ShiTMSubroutine.run

/-- The checker input for `(x, w)`. -/
def chkInput (x w : List Bool) : List (tm.Γ tm.k₀) := (PvsNP.encodePair (x, w)).map ein.symm

theorem length_chkInput (x w : List Bool) :
    (chkInput tm ein x w).length = x.length + w.length := by
  simp [chkInput, PvsNP.encodePair]

/-- Steps 1: preparation of the checker input. -/
theorem iter_prep (x w c : List Bool) (B : ℕ) (hB : 2 * (x.length + w.length) + c.length ≤ B) :
    SegE M (wc (W .prepA) (false, false) (nochk tm) (rg x [] w c [] [] []))
      (wc (.inl tm.main) (false, false) (initList tm (chkInput tm ein x w)).stk
        (rg x [] w c [] [] [])) B := by
  have hsz : ∀ L : List (tm.Γ tm.k₀), ShiTMStackGrowth.size (Function.update (nochk tm) tm.k₀ L) =
      L.length := by
    intro L
    have := size_update (nochk tm) tm.k₀ L
    rw [size_nochk] at this; simpa [nochk] using this
  have h1 : SegE M (wc (W .prepA) (false, false) (nochk tm) (rg x [] w c [] [] []))
      (wc (W .prepB) (false, false) (nochk tm) (rg x [] [] c w.reverse [] [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_one (by simp)) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_one _ _ _ (by simp)]; simp; regs_eq
    · simp [size_nochk, len_rg]; omega
    · simp [size_nochk, len_rg]; omega
  have h2 : SegE M (wc (W .prepB) (false, false) (nochk tm) (rg x [] [] c w.reverse [] []))
      (wc (W .prepC) (false, false)
        (Function.update (nochk tm) tm.k₀ (w.map fun b => ein.symm (.inr b)))
        (rg x [] w c [] [] [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_two (by simp) (by simp)) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_two _ _ _ _ _ (by simp) (by simp) (by simp)]
      simp only [update_join_get, update_join_inl]
      join_eq
    · simp [size_nochk, len_rg]; omega
    · rw [hsz]; simp [len_rg]; omega
  have h3 : SegE M (wc (W .prepC) (false, false)
        (Function.update (nochk tm) tm.k₀ (w.map fun b => ein.symm (.inr b)))
        (rg x [] w c [] [] []))
      (wc (W .prepD) (false, false)
        (Function.update (nochk tm) tm.k₀ (w.map fun b => ein.symm (.inr b)))
        (rg [] [] w c x.reverse [] [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_one (by simp)) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_one _ _ _ (by simp)]; simp; regs_eq
    · rw [hsz]; simp [len_rg]; omega
    · rw [hsz]; simp [len_rg]; omega
  have h4 : SegE M (wc (W .prepD) (false, false)
        (Function.update (nochk tm) tm.k₀ (w.map fun b => ein.symm (.inr b)))
        (rg [] [] w c x.reverse [] []))
      (wc (.inl tm.main) (false, false) (initList tm (chkInput tm ein x w)).stk
        (rg x [] w c [] [] [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_two (by simp) (by simp)) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_two _ _ _ _ _ (by simp) (by simp) (by simp), initList_stk_eq]
      simp only [update_join_get, update_join_inl]
      congr 1
      · simp [chkInput, PvsNP.encodePair, Function.update_idem]; rfl
      · funext e; cases e <;> simp [Regs.get]
    · rw [hsz]; simp [len_rg]; omega
    · rw [initList_stk_eq, hsz, length_chkInput]; simp [len_rg]; omega
  exact h1.trans (h2.trans (h3.trans h4))

/-- Step 2: the embedded checker run. The peak is the checker peak plus the registers. -/
theorem iter_check (I : List (tm.Γ tm.k₀)) (ys : List (tm.Γ tm.k₁)) (R : Regs)
    (hout : TM2Outputs tm I (some ys)) (Bchk : ℕ) (hsp : SpaceBoundedOn tm I Bchk) :
    SegE M (wc (.inl tm.main) (false, false) (initList tm I).stk R)
      (wc (W .ans) (false, false) (haltList tm ys).stk R) (Bchk + R.len) := by
  have h := seg_emb Sum.inl (W .ans : EL tm k) M tm.m (fun _ => rfl) (false, false) R.get
    (initList tm I) (haltList tm ys) hout.steps hout.evals_in_steps Bchk
    (fun t _ e he => hsp t e he)
  rw [Regs.extSize_get] at h
  exact ⟨_, h⟩

/-- Step 3: pop the checker answer; every checker stack is now empty. -/
theorem iter_ans (b : Bool) (R : Regs) (B : ℕ) (hB : 1 + R.len ≤ B) :
    SegE M (wc (W .ans) (false, false) (haltList tm [eout.symm b]).stk R)
      (wc (if b then W .incC else W .incW) (b, true) (nochk tm) R) B := by
  refine SegE.single ?_ ?_ ?_
  · simp only [step, prog, wprog, stepAux, wc, join_inl, haltList_stk_self, update_join_inl,
      List.head?_cons, List.tail_cons, Option.map_some, Option.getD_some,
      Equiv.apply_symm_apply]
    rw [show Function.update (haltList tm [eout.symm b]).stk tm.k₁ [] = nochk tm from
      haltList_pop tm _]
    cases b <;> rfl
  · rw [size_wc]
    have : ShiTMStackGrowth.size (haltList tm [eout.symm b]).stk = 1 := cfgSpace_haltList tm _
    omega
  · rw [size_wc, size_nochk]; omega

theorem incAt_cnt : IncAt (prog tm ein eout k) .cnt .tmp (W .incC) (W .incCno) (W .incCov)
    (W .incW) (W .incW) := ⟨by decide, rfl, rfl, rfl⟩

theorem incAt_wit : IncAt (prog tm ein eout k) .wit .tmp (W .incW) (W .incWno) (W .incWov)
    (W .prepA) (W .finA) := ⟨by decide, rfl, rfl, rfl⟩

/-- Step 4: count an accepted witness. -/
theorem iter_incC (x w c : List Bool) (r : Reg) (B : ℕ)
    (hB : x.length + w.length + c.length ≤ B) :
    SegE M (wc (W .incC) r (nochk tm) (rg x [] w c [] [] []))
      (wc (W .incW) (false, false) (nochk tm) (rg x [] w (inc c).1 [] [] [])) B := by
  have h := inc_seg (incAt_cnt tm ein eout k) c 0 tm.initialState r
    (join (nochk tm) (rg x [] w c [] [] []).get) rfl rfl
  rw [ite_self] at h
  have hout : incOut .cnt .tmp 0 c (join (nochk tm) (rg x [] w c [] [] []).get) =
      join (nochk tm) (rg x [] w (inc c).1 [] [] []).get := by
    unfold incOut; simp; regs_eq
  rw [hout] at h
  refine ⟨_, h.mono ?_⟩
  rw [size_join, show (∑ e, ((rg x [] w c [] [] []).get e).length) = (rg x [] w c [] [] []).len
    from Regs.extSize_get _, size_nochk, len_rg]
  simp; omega

/-- Step 5: advance the witness; overflow leaves the loop. -/
theorem iter_incW (x w c : List Bool) (r : Reg) (B : ℕ)
    (hB : x.length + w.length + c.length ≤ B) :
    SegE M (wc (W .incW) r (nochk tm) (rg x [] w c [] [] []))
      (wc (if (inc w).2 then W .finA else W .prepA) (false, false) (nochk tm)
        (rg x [] (inc w).1 c [] [] [])) B := by
  have h := inc_seg (incAt_wit tm ein eout k) w 0 tm.initialState r
    (join (nochk tm) (rg x [] w c [] [] []).get) rfl rfl
  have hout : incOut .wit .tmp 0 w (join (nochk tm) (rg x [] w c [] [] []).get) =
      join (nochk tm) (rg x [] (inc w).1 c [] [] []).get := by
    unfold incOut; simp; regs_eq
  rw [hout] at h
  refine ⟨_, h.mono ?_⟩
  rw [size_join, show (∑ e, ((rg x [] w c [] [] []).get e).length) = (rg x [] w c [] [] []).len
    from Regs.extSize_get _, size_nochk, len_rg]
  simp; omega

/-- **One loop iteration.** -/
theorem iter_seg (R : PvsNP.Str × PvsNP.Str → Bool) (x w c : List Bool)
    (hout : TM2Outputs tm (chkInput tm ein x w) (some [eout.symm (R (x, w))])) (Bchk : ℕ)
    (hsp : SpaceBoundedOn tm (chkInput tm ein x w) Bchk) (B : ℕ)
    (hB : Bchk + 2 * (x.length + w.length) + c.length ≤ B) :
    SegE M (wc (W .prepA) (false, false) (nochk tm) (rg x [] w c [] [] []))
      (wc (if (inc w).2 then W .finA else W .prepA) (false, false) (nochk tm)
        (rg x [] (inc w).1 (if R (x, w) then (inc c).1 else c) [] [] [])) B := by
  have hone : 1 ≤ Bchk := by simpa using hsp.output_le hout
  have h1 := iter_prep tm ein eout k x w c B (by omega)
  have h2 := (iter_check tm ein eout k _ _ (rg x [] w c [] [] []) hout Bchk hsp).mono
    (show Bchk + (rg x [] w c [] [] []).len ≤ B by simp [len_rg]; omega)
  have h3 := iter_ans tm ein eout k (R (x, w)) (rg x [] w c [] [] []) B
    (by simp [len_rg]; omega)
  have h12 := h1.trans (h2.trans h3)
  cases hR : R (x, w) with
  | true =>
      rw [hR] at h12
      have h4 := iter_incC tm ein eout k x w c (true, true) B (by omega)
      have h5 := iter_incW tm ein eout k x w (inc c).1 (false, false) B (by simp; omega)
      exact h12.trans (h4.trans h5)
  | false =>
      rw [hR] at h12
      have h5 := iter_incW tm ein eout k x w c (false, true) B (by omega)
      exact h12.trans h5

end ShiPPPSPACE
