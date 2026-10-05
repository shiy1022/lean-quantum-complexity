/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

PP ⊆ PSPACE in the corrected finite-multistack space model (plan tasks S13–S15).
-/
import Machine.EnumFinal
import Space.TimeToSpace
import Count.Enumeration

set_option autoImplicit false

/-!
# `PP ⊆ PSPACE`

For a PP language with checker `R` (certificate `c`) and exponent `k`, the enumerator
`machine c.tm c.inputAlphabet c.outputAlphabet k` halts on every input `x` with the single
output bit `2 * countAccept R x (n^k) > 2^(n^k)`, and every configuration it ever reaches has
total stack length at most

  `4 (n + 1) + 4 (n + 1)^k + T(n + n^k) * D`,

where `T` is the checker's time polynomial and `D` its per-step stack-growth constant. The
bound is a maximum over phases, not a sum over the `2^(n^k)` iterations: each iteration
restores the loop-head invariant and reuses the same scratch space.
-/

namespace ShiPPPSPACE

open Turing ShiSpace PvsNP

/-- The predicate decided for a PP witness `(R, k)`. -/
def ppχ (R : Str × Str → Bool) (k : ℕ) (x : Str) : Bool :=
  decide (2 * ShiClassPP.countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k))

section

variable {R : Str × Str → Bool} (c : TM2ComputableInPolyTime encodePair Computability.encodeBool R)
  (k : ℕ)

local notation "M" => prog c.tm c.inputAlphabet c.outputAlphabet k
local notation "E" => machine c.tm c.inputAlphabet c.outputAlphabet k

/-- Loop head before witness `j`. -/
def head (x : Str) (m j : ℕ) : Turing.TM2.Cfg (HG c.tm.Γ) (EL c.tm k) (c.tm.σ × Reg) :=
  wc (W .prepA) (false, false) (nochk c.tm)
    (rg x [] (word m j) (word (m + 1) (ShiPPPSPACE.prefixCount R x m j)) [] [] [])

/-- The space bound for inputs of length `n`. -/
def bound (D n : ℕ) : ℕ := 4 * (n + 1) + 4 * (n + 1) ^ k + c.time.eval (n + n ^ k) * D

variable {c k}

/-- One iteration in terms of the enumeration specification. -/
theorem head_step (D : ℕ) (hD : ∀ l v S, ShiTMStackGrowth.size (TM2.stepAux (c.tm.m l) v S).stk ≤
      ShiTMStackGrowth.size S + D) (x : Str) (j : ℕ) (hj : j < 2 ^ (x.length ^ k)) :
    SegE M (head c k x (x.length ^ k) j)
      (wc (if j + 1 = 2 ^ (x.length ^ k) then W .finA else W .prepA) (false, false) (nochk c.tm)
        (rg x [] (word (x.length ^ k) (j + 1))
          (word (x.length ^ k + 1) (ShiPPPSPACE.prefixCount R x (x.length ^ k) (j + 1)))
          [] [] [])) (bound c k D x.length) := by
  set m := x.length ^ k with hm
  set w := word m j
  have hout := (c.outputsFun (x, w)).toTM2Outputs
  have hsp := spaceBoundedOn_of_outputsInTime c.tm D hD (c.outputsFun (x, w))
  have hlen : (encodePair (x, w)).length = x.length + m := by
    simp [encodePair, w]
  have hilen : (List.map c.inputAlphabet.invFun (encodePair (x, w))).length = x.length + m := by
    simp [hlen]
  rw [hilen, hlen] at hsp
  have hmle := pow_le_succ_pow x.length k k le_rfl
  have h := iter_seg c.tm c.inputAlphabet c.outputAlphabet k R x w
    (word (m + 1) (ShiPPPSPACE.prefixCount R x m j)) hout _ hsp
    (bound c k D x.length) (by
      unfold bound
      simp only [length_word, w]
      rw [← hm]
      omega)
  have ha : ShiPPPSPACE.prefixCount R x m j < 2 ^ m :=
    lt_of_le_of_lt (prefixCount_le R x m j) hj
  have hw := inc_word m j hj
  have hc := inc_word (m + 1) (ShiPPPSPACE.prefixCount R x m j) (by rw [pow_succ]; omega)
  rw [hw] at h
  simp only at h
  have hcnt : (if R (x, w) = true then
      (word (m + 1) (ShiPPPSPACE.prefixCount R x m j + 1),
        decide (ShiPPPSPACE.prefixCount R x m j + 1 = 2 ^ (m + 1))).1
      else word (m + 1) (ShiPPPSPACE.prefixCount R x m j)) =
      word (m + 1) (ShiPPPSPACE.prefixCount R x m (j + 1)) := by
    rw [prefixCount_succ]
    cases R (x, w) <;> simp
  rw [hc, hcnt] at h
  convert h using 3
  all_goals first | rfl | simp

/-- All iterations up to witness `j`. -/
theorem head_upto (D : ℕ) (hD : ∀ l v S, ShiTMStackGrowth.size (TM2.stepAux (c.tm.m l) v S).stk ≤
      ShiTMStackGrowth.size S + D) (x : Str) (j : ℕ) (hj : j < 2 ^ (x.length ^ k)) :
    SegE M (head c k x (x.length ^ k) 0) (head c k x (x.length ^ k) j) (bound c k D x.length) := by
  induction j with
  | zero =>
      refine SegE.refl ?_
      rw [head, size_wc, size_nochk, len_rg]
      have := pow_le_succ_pow x.length k k le_rfl
      simp only [List.length_nil, length_word]
      unfold bound
      omega
  | succ j ih =>
      have h1 := ih (by omega)
      have h2 := head_step (k := k) D hD x j (by omega)
      rw [if_neg (by omega)] at h2
      exact h1.trans h2

/-- **The whole run** from the initial to the halting configuration. -/
theorem full_run (D : ℕ) (hD : ∀ l v S, ShiTMStackGrowth.size (TM2.stepAux (c.tm.m l) v S).stk ≤
      ShiTMStackGrowth.size S + D) (x : Str) :
    SegE M (initList E x) (haltList E [ppχ R k x]) (bound c k D x.length) := by
  have hmle := pow_le_succ_pow x.length k k le_rfl
  have hpos : 0 < 2 ^ (x.length ^ k) := by positivity
  have h0 := init_seg c.tm c.inputAlphabet c.outputAlphabet k x (bound c k D x.length)
    (by unfold bound; omega)
  have hH0 : wc (W .prepA) (false, false) (nochk c.tm)
      (rg x [] (List.replicate (x.length ^ k) false) (List.replicate (x.length ^ k + 1) false)
        [] [] []) = head c k x (x.length ^ k) 0 := by
    simp [head, word_zero]
  rw [hH0, ← initList_machine c.tm c.inputAlphabet c.outputAlphabet k x] at h0
  have h1 := head_upto (k := k) D hD x (2 ^ (x.length ^ k) - 1) (by omega)
  have h2 := head_step (k := k) D hD x (2 ^ (x.length ^ k) - 1) (by omega)
  rw [if_pos (by omega), show 2 ^ (x.length ^ k) - 1 + 1 = 2 ^ (x.length ^ k) by omega] at h2
  have h3 := final_seg c.tm c.inputAlphabet c.outputAlphabet k x
    (word (x.length ^ k) (2 ^ (x.length ^ k)))
    (word (x.length ^ k + 1) (ShiPPPSPACE.prefixCount R x (x.length ^ k) (2 ^ (x.length ^ k))))
    (bound c k D x.length) (by simp only [length_word]; unfold bound; omega)
  have hans : answer (scanAll (false, false, false)
      (word (x.length ^ k + 1)
        (ShiPPPSPACE.prefixCount R x (x.length ^ k) (2 ^ (x.length ^ k))))) = ppχ R k x := by
    rw [answer_scanAll (x.length ^ k) _ (length_word _ _), val_word_of_lt _ _
      (prefixCount_lt R x (x.length ^ k) _ le_rfl), prefixCount_full]
    rfl
  rw [hans] at h3
  have h3' := SegE.cast h3 (haltList_machine c.tm c.inputAlphabet c.outputAlphabet k (ppχ R k x)).symm
  exact h0.trans (h1.trans (h2.trans h3'))

end

/-- The space polynomial: `4 (X + 1) + 4 (X + 1)^k + T.comp (X + X^k) * D`. -/
noncomputable def boundPoly (T : Polynomial ℕ) (k D : ℕ) : Polynomial ℕ :=
  Polynomial.C 4 * (Polynomial.X + 1) + Polynomial.C 4 * (Polynomial.X + 1) ^ k +
    T.comp (Polynomial.X + Polynomial.X ^ k) * Polynomial.C D

theorem eval_boundPoly (T : Polynomial ℕ) (k D n : ℕ) :
    (boundPoly T k D).eval n = 4 * (n + 1) + 4 * (n + 1) ^ k + T.eval (n + n ^ k) * D := by
  simp [boundPoly, Polynomial.eval_comp]

/-- The enumerator as a total computation of `ppχ R k`. -/
noncomputable def decider {R : Str × Str → Bool}
    (c : TM2ComputableInPolyTime encodePair Computability.encodeBool R) (k : ℕ) :
    TM2Computable (id : List Bool → List Bool) Computability.encodeBool (ppχ R k) where
  tm := machine c.tm c.inputAlphabet c.outputAlphabet k
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  outputsFun x :=
    -- `TM2Outputs` is data: choose the proved growth constant and run length.
    have h := full_run (c := c) (k := k) _ (exists_growth c.tm).choose_spec x
    have hx : (List.map (Equiv.refl Bool).invFun (id x) : List ((machine c.tm c.inputAlphabet
        c.outputAlphabet k).Γ (machine c.tm c.inputAlphabet c.outputAlphabet k).k₀)) =
        (x : List ((machine c.tm c.inputAlphabet c.outputAlphabet k).Γ
          (machine c.tm c.inputAlphabet c.outputAlphabet k).k₀)) := List.map_id x
    ⟨h.choose, by rw [hx]; exact h.choose_spec.1⟩

/-- **The PP-to-PSPACE construction.** -/
theorem polySpaceDecider_ppχ {R : Str × Str → Bool} (hR : PolyTimeChecker R) (k : ℕ) :
    PolySpaceDecider (ppχ R k) := by
  obtain ⟨c⟩ := hR
  obtain ⟨D, hD⟩ := exists_growth c.tm
  refine ⟨decider c k, boundPoly c.time k D, fun x => ?_⟩
  have hx : (List.map (decider c k).inputAlphabet.invFun x : List ((decider c k).tm.Γ
      (decider c k).tm.k₀)) = (x : List ((decider c k).tm.Γ (decider c k).tm.k₀)) := List.map_id x
  rw [hx, eval_boundPoly]
  obtain ⟨n, h⟩ := full_run D hD x
  exact h.forall_of_halted rfl

end ShiPPPSPACE

/-- **`PP ⊆ PSPACE`** in the corrected finite-multistack space model. -/
theorem ShiSpace.pp_subset_pspace : ShiClassPP.PP ⊆ ShiSpace.PSPACE := by
  rintro L ⟨R, k, hR, hL⟩
  refine ⟨ShiPPPSPACE.ppχ R k, ShiPPPSPACE.polySpaceDecider_ppχ hR k, fun x => ?_⟩
  rw [hL x]
  simp [ShiPPPSPACE.ppχ]
