/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The final phase and the initial/halting configurations of the enumerator (plan task S13).
-/
import Machine.EnumLoop

set_option autoImplicit false

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ (Bool ⊕ Bool)) (eout : tm.Γ tm.k₁ ≃ Bool) (k : ℕ)

local notation "M" => prog tm ein eout k
local notation "E" => machine tm ein eout k

/-- The initial configuration of the enumerator on `x`. -/
theorem initList_machine (x : List Bool) :
    initList E x = wc (W .lenA) (false, false) (nochk tm) (rg x [] [] [] [] [] []) := by
  have hstk : (initList E x).stk = join (nochk tm) (rg x [] [] [] [] [] []).get := by
    funext i
    rcases i with j | e
    · exact initList_stk_ne E x (.inl j) (by simp [machine])
    · cases e
      · exact initList_stk_self E x
      all_goals exact initList_stk_ne E x _ (by simp [machine])
  simp only [wc, ← hstk]
  rfl

/-- The halting configuration of the enumerator with answer `a`. -/
theorem haltList_machine (a : Bool) :
    haltList E [a] = ⟨none, (tm.initialState, (false, false)),
      join (nochk tm) (rg [] [a] [] [] [] [] []).get⟩ := by
  have hstk : (haltList E [a]).stk = join (nochk tm) (rg [] [a] [] [] [] [] []).get := by
    funext i
    rcases i with j | e
    · exact haltList_stk_ne E [a] (.inl j) (by simp [machine])
    · cases e
      case out => exact haltList_stk_self E [a]
      all_goals exact haltList_stk_ne E [a] _ (by simp [machine])
  rw [← hstk]
  rfl

/-- **Final phase.** Clear `wit` and `inp`, scan the counter, halt. -/
theorem final_seg (x w c : List Bool) (B : ℕ) (hB : x.length + w.length + c.length + 1 ≤ B) :
    SegE M (wc (W .finA) (false, false) (nochk tm) (rg x [] w c [] [] []))
      ⟨none, (tm.initialState, (false, false)),
        join (nochk tm) (rg [] [answer (scanAll (false, false, false) c)] [] [] [] [] []).get⟩ B := by
  have h1 : SegE M (wc (W .finA) (false, false) (nochk tm) (rg x [] w c [] [] []))
      (wc (W .finB) (false, false) (nochk tm) (rg x [] [] c [] [] [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_nil _) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_clear]; simp; regs_eq
    · simp [size_nochk, len_rg]; omega
    · simp [size_nochk, len_rg]; omega
  have h2 : SegE M (wc (W .finB) (false, false) (nochk tm) (rg x [] [] c [] [] []))
      (wc (W (.scan (false, false, false))) (false, false) (nochk tm) (rg [] [] [] c [] [] [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_nil _) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_clear]; simp; regs_eq
    · simp [size_nochk, len_rg]; omega
    · simp [size_nochk, len_rg]; omega
  have h3 := scan_seg M .cnt .out (fun st => W (.scan st)) (W .finH) (by decide) (fun _ => rfl)
    c (false, false, false) tm.initialState (false, false)
    (join (nochk tm) (rg [] [] [] c [] [] []).get) rfl
  have hout : scanOut .cnt .out (false, false, false) c (join (nochk tm) (rg [] [] [] c [] [] []).get) =
      join (nochk tm) (rg [] [answer (scanAll (false, false, false) c)] [] [] [] [] []).get := by
    unfold scanOut; simp; regs_eq
  rw [hout] at h3
  have h3' : SegE M (wc (W (.scan (false, false, false))) (false, false) (nochk tm)
      (rg [] [] [] c [] [] []))
      (wc (W .finH) (false, false) (nochk tm)
        (rg [] [answer (scanAll (false, false, false) c)] [] [] [] [] [])) B := by
    refine ⟨_, h3.mono ?_⟩
    rw [size_join, show (∑ e, ((rg [] [] [] c [] [] []).get e).length) =
      (rg [] [] [] c [] [] []).len from Regs.extSize_get _, size_nochk, len_rg]
    simp; omega
  have h4 : SegE M (wc (W .finH) (false, false) (nochk tm)
        (rg [] [answer (scanAll (false, false, false) c)] [] [] [] [] []))
      ⟨none, (tm.initialState, (false, false)),
        join (nochk tm) (rg [] [answer (scanAll (false, false, false) c)] [] [] [] [] []).get⟩ B := by
    refine SegE.single rfl ?_ ?_
    · rw [size_wc, size_nochk, len_rg]; simp; omega
    · show ShiTMStackGrowth.size (join _ _) ≤ B
      rw [size_join, show (∑ e, ((rg [] [answer (scanAll (false, false, false) c)] [] [] [] [] []).get
        e).length) = (rg [] [answer (scanAll (false, false, false) c)] [] [] [] [] []).len
        from Regs.extSize_get _, size_nochk, len_rg]
      simp; omega
  exact h1.trans (h2.trans (h3'.trans h4))

end ShiPPPSPACE
