/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The initialization phase of the enumerator (plan task S09).
-/
import Machine.EnumBasics

set_option autoImplicit false

/-!
# Initialization: `wit = 0^(n^k)` and `cnt = 0^(n^k+1)`

From the initial configuration on input `x` (length `n`), the machine reaches the loop head
`prepA` with `inp = x`, `wit = 0^m`, `cnt = 0^(m+1)` and every other stack empty, where
`m = n^k`. Every configuration on the way is within any bound `B` that dominates
`3 * (n + 1) + 3 * (n + 1)^k`; nothing exponential is ever allocated.
-/

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

/-- Register contents by name. -/
abbrev rg (inp out wit cnt tmp nn pq : List Bool) : Regs := ⟨inp, out, wit, cnt, tmp, nn, pq⟩

theorem len_rg (inp out wit cnt tmp nn pq : List Bool) :
    (rg inp out wit cnt tmp nn pq).len = inp.length + out.length + wit.length + cnt.length +
      tmp.length + nn.length + pq.length := rfl

/-- Entry label of multiplication round `i` (or the counter phase after the last round). -/
def entryL (tm : FinTM2) (k i : ℕ) : EL tm k :=
  if h : i < k then W (.mulPop ⟨i, h⟩) else W .cntA

theorem pow_le_succ_pow (n i k : ℕ) (h : i ≤ k) : n ^ i ≤ (n + 1) ^ k :=
  le_trans (Nat.pow_le_pow_left (Nat.le_succ n) i) (Nat.pow_le_pow_right (Nat.succ_pos n) h)

variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ (Bool ⊕ Bool)) (eout : tm.Γ tm.k₁ ≃ Bool) (k : ℕ)

local notation "M" => prog tm ein eout k

theorem init_lenA (x : List Bool) (r : Reg) (B : ℕ) (hB : 2 * x.length ≤ B) :
    SegE M (wc (W .lenA) r (nochk tm) (rg x [] [] [] [] [] []))
      (wc (W .lenB) (false, false) (nochk tm) (rg [] [] [] [] x.reverse [] [])) B := by
  refine segE_loop tm ein eout k rfl (avoids_one (by simp)) r _ _ _ _ ?_ B ?_ ?_
  · rw [loopOut_one _ _ _ (by simp)]
    simp
    regs_eq
  · simp [size_nochk, len_rg]; omega
  · simp [size_nochk, len_rg]; omega

theorem init_lenB (x : List Bool) (r : Reg) (B : ℕ) (hB : 2 * x.length ≤ B) :
    SegE M (wc (W .lenB) r (nochk tm) (rg [] [] [] [] x.reverse [] []))
      (wc (W .seed) (false, false) (nochk tm)
        (rg x [] [] [] [] (List.replicate x.length false) [])) B := by
  refine segE_loop tm ein eout k rfl (avoids_two (by simp) (by simp)) r _ _ _ _ ?_ B ?_ ?_
  · rw [loopOut_two _ _ _ _ _ (by simp) (by simp) (by simp)]
    simp
    regs_eq
  · simp [size_nochk, len_rg]; omega
  · simp [size_nochk, len_rg]; omega

theorem init_seed (x nnL : List Bool) (r : Reg) (B : ℕ) (hB : x.length + nnL.length + 1 ≤ B) :
    SegE M (wc (W .seed) r (nochk tm) (rg x [] [] [] [] nnL []))
      (wc (entryL tm k 0) r (nochk tm) (rg x [] [false] [] [] nnL [])) B := by
  refine segE_step tm ein eout k ?_ B ?_ ?_
  · simp only [step, prog, wprog, stepAux, wc, entryL]
    congr 2
    simp
    regs_eq
  · simp [size_nochk, len_rg]; omega
  · simp [size_nochk, len_rg]; omega

theorem init_mulPop_cons (i : Fin k) (x w nnL pqL : List Bool) (b : Bool) (r : Reg) (B : ℕ)
    (hB : x.length + w.length + 1 + nnL.length + pqL.length ≤ B) :
    SegE M (wc (W (.mulPop i)) r (nochk tm) (rg x [] (b :: w) [] [] nnL pqL))
      (wc (W (.mulA i)) (b, true) (nochk tm) (rg x [] w [] [] nnL pqL)) B := by
  refine segE_step tm ein eout k ?_ B ?_ ?_
  · simp only [step, prog, wprog, popBit, stepAux, wc]
    simp
    regs_eq
  · simp [size_nochk, len_rg]; omega
  · simp [size_nochk, len_rg]; omega

theorem init_mulPop_nil (i : Fin k) (x nnL pqL : List Bool) (r : Reg) (B : ℕ)
    (hB : x.length + nnL.length + pqL.length ≤ B) :
    SegE M (wc (W (.mulPop i)) r (nochk tm) (rg x [] [] [] [] nnL pqL))
      (wc (W (.mulMove i)) (false, false) (nochk tm) (rg x [] [] [] [] nnL pqL)) B := by
  refine segE_step tm ein eout k ?_ B ?_ ?_
  · simp only [step, prog, wprog, popBit, stepAux, wc]
    simp
    regs_eq
  · simp [size_nochk, len_rg]; omega
  · simp [size_nochk, len_rg]; omega

/-- One multiplication round adds `n` to the product register per popped symbol. -/
theorem init_round (i : Fin k) (x : List Bool) (a q : ℕ) (r : Reg) (B : ℕ)
    (hB : 3 * x.length + a + q + a * x.length ≤ B) :
    SegE M (wc (W (.mulPop i)) r (nochk tm)
        (rg x [] (List.replicate a false) [] [] (List.replicate x.length false)
          (List.replicate q false)))
      (wc (W (.mulMove i)) (false, false) (nochk tm)
        (rg x [] [] [] [] (List.replicate x.length false)
          (List.replicate (q + a * x.length) false))) B := by
  induction a generalizing q r with
  | zero =>
      simpa using init_mulPop_nil tm ein eout k i x _ _ r B (by simp; omega)
  | succ a ih =>
      rw [List.replicate_succ]
      have hmul : (a + 1) * x.length = a * x.length + x.length := Nat.succ_mul a x.length
      have h1 := init_mulPop_cons tm ein eout k i x (List.replicate a false)
        (List.replicate x.length false) (List.replicate q false) false r B (by simp; omega)
      have h2 : SegE M (wc (W (.mulA i)) (false, true) (nochk tm)
          (rg x [] (List.replicate a false) [] [] (List.replicate x.length false)
            (List.replicate q false)))
          (wc (W (.mulB i)) (false, false) (nochk tm)
          (rg x [] (List.replicate a false) [] (List.replicate x.length false) []
            (List.replicate q false))) B := by
        refine segE_loop tm ein eout k rfl (avoids_one (by simp)) _ _ _ _ _ ?_ B ?_ ?_
        · rw [loopOut_one _ _ _ (by simp)]
          simp
          regs_eq
        · simp [size_nochk, len_rg]; omega
        · simp [size_nochk, len_rg]; omega
      have h3 : SegE M (wc (W (.mulB i)) (false, false) (nochk tm)
          (rg x [] (List.replicate a false) [] (List.replicate x.length false) []
            (List.replicate q false)))
          (wc (W (.mulPop i)) (false, false) (nochk tm)
          (rg x [] (List.replicate a false) [] [] (List.replicate x.length false)
            (List.replicate (x.length + q) false))) B := by
        refine segE_loop tm ein eout k rfl (avoids_two (by simp) (by simp)) _ _ _ _ _ ?_ B ?_ ?_
        · rw [loopOut_two _ _ _ _ _ (by simp) (by simp) (by simp)]
          simp
          regs_eq
        · simp [size_nochk, len_rg]; omega
        · simp [size_nochk, len_rg]; omega
      have h4 := ih (x.length + q) (false, false) (by omega)
      have e : x.length + q + a * x.length = q + (a + 1) * x.length := by rw [hmul]; omega
      rw [e] at h4
      exact h1.trans (h2.trans (h3.trans h4))

theorem init_mulMove (i : Fin k) (x : List Bool) (p : ℕ) (r : Reg) (B : ℕ)
    (hB : 2 * x.length + p ≤ B) :
    SegE M (wc (W (.mulMove i)) r (nochk tm)
        (rg x [] [] [] [] (List.replicate x.length false) (List.replicate p false)))
      (wc (entryL tm k (i.val + 1)) (false, false) (nochk tm)
        (rg x [] (List.replicate p false) [] [] (List.replicate x.length false) [])) B := by
  refine segE_loop tm ein eout k rfl (avoids_one (by simp)) _ _ _ _ _ ?_ B ?_ ?_
  · rw [loopOut_one _ _ _ (by simp)]
    simp
    regs_eq
  · simp [size_nochk, len_rg]; omega
  · simp [size_nochk, len_rg]; omega

/-- After `i ≤ k` rounds the product register holds `0^(n^i)`. -/
theorem init_rounds (x : List Bool) (B : ℕ)
    (hB : 3 * (x.length + 1) + 3 * (x.length + 1) ^ k ≤ B) (i : ℕ) (hi : i ≤ k) :
    SegE M (wc (entryL tm k 0) (false, false) (nochk tm)
        (rg x [] [false] [] [] (List.replicate x.length false) []))
      (wc (entryL tm k i) (false, false) (nochk tm)
        (rg x [] (List.replicate (x.length ^ i) false) [] []
          (List.replicate x.length false) [])) B := by
  induction i with
  | zero =>
      refine SegE.refl ?_
      rw [size_wc]; simp [size_nochk, len_rg]; omega
  | succ i ih =>
      have hik : i < k := by omega
      have h1 := ih (by omega)
      have hent : entryL tm k i = W (.mulPop ⟨i, hik⟩) := by simp [entryL, hik]
      rw [hent] at h1
      have hp1 := pow_le_succ_pow x.length i k (by omega)
      have hp2 := pow_le_succ_pow x.length (i + 1) k (by omega)
      rw [pow_succ] at hp2
      have h2 := init_round tm ein eout k ⟨i, hik⟩ x (x.length ^ i) 0 (false, false) B
        (by omega)
      have h3 := init_mulMove tm ein eout k ⟨i, hik⟩ x (0 + x.length ^ i * x.length)
        (false, false) B (by omega)
      simp only [zero_add] at h2 h3
      rw [← pow_succ] at h2 h3
      exact h1.trans (h2.trans h3)

/-- **Initialization.** -/
theorem init_seg (x : List Bool) (B : ℕ)
    (hB : 3 * (x.length + 1) + 3 * (x.length + 1) ^ k ≤ B) :
    SegE M (wc (W .lenA) (false, false) (nochk tm) (rg x [] [] [] [] [] []))
      (wc (W .prepA) (false, false) (nochk tm)
        (rg x [] (List.replicate (x.length ^ k) false)
          (List.replicate (x.length ^ k + 1) false) [] [] [])) B := by
  have hm := pow_le_succ_pow x.length k k le_rfl
  have h1 := init_lenA tm ein eout k x (false, false) B (by omega)
  have h2 := init_lenB tm ein eout k x (false, false) B (by omega)
  have h3 := init_seed tm ein eout k x (List.replicate x.length false) (false, false) B
    (by simp; omega)
  have h4 := init_rounds tm ein eout k x B hB k le_rfl
  have hent : entryL tm k k = W .cntA := by simp [entryL]
  rw [hent] at h4
  set m := x.length ^ k
  have h5 : SegE M (wc (W .cntA) (false, false) (nochk tm)
      (rg x [] (List.replicate m false) [] [] (List.replicate x.length false) []))
      (wc (W .cntB) (false, false) (nochk tm)
      (rg x [] [] [] (List.replicate m false) (List.replicate x.length false) [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_one (by simp)) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_one _ _ _ (by simp)]
      simp
      regs_eq
    · simp [size_nochk, len_rg]; omega
    · simp [size_nochk, len_rg]; omega
  have h6 : SegE M (wc (W .cntB) (false, false) (nochk tm)
      (rg x [] [] [] (List.replicate m false) (List.replicate x.length false) []))
      (wc (W .cntOne) (false, false) (nochk tm)
      (rg x [] (List.replicate m false) (List.replicate m false) []
        (List.replicate x.length false) [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_two (by simp) (by simp)) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_two _ _ _ _ _ (by simp) (by simp) (by simp)]
      simp
      regs_eq
    · simp [size_nochk, len_rg]; omega
    · simp [size_nochk, len_rg]; omega
  have h7 : SegE M (wc (W .cntOne) (false, false) (nochk tm)
      (rg x [] (List.replicate m false) (List.replicate m false) []
        (List.replicate x.length false) []))
      (wc (W .clrN) (false, false) (nochk tm)
      (rg x [] (List.replicate m false) (List.replicate (m + 1) false) []
        (List.replicate x.length false) [])) B := by
    refine segE_step tm ein eout k ?_ B ?_ ?_
    · simp only [step, prog, wprog, stepAux, wc]
      simp [List.replicate_succ]
      regs_eq
    · simp [size_nochk, len_rg]; omega
    · simp [size_nochk, len_rg]; omega
  have h8 : SegE M (wc (W .clrN) (false, false) (nochk tm)
      (rg x [] (List.replicate m false) (List.replicate (m + 1) false) []
        (List.replicate x.length false) []))
      (wc (W .prepA) (false, false) (nochk tm)
      (rg x [] (List.replicate m false) (List.replicate (m + 1) false) [] [] [])) B := by
    refine segE_loop tm ein eout k rfl (avoids_nil _) _ _ _ _ _ ?_ B ?_ ?_
    · rw [loopOut_clear]
      simp
      regs_eq
    · simp [size_nochk, len_rg]; omega
    · simp [size_nochk, len_rg]; omega
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))

end ShiPPPSPACE
