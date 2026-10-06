/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Circuit.Controlled
import QIP.ValidGates

/-!
# Q28 — the zero test

`ztGates c t S anc` flips `t` exactly when the control `c` is set and every wire of `S` reads `0`,
using one clean ancilla per wire of `S`, all returned to `0` (**`runLayer_zt`**). It is a ladder
of "negated-control AND" steps `X s; Toffoli(c, s, a); X s` (`runLayer_nca`), uncomputed in
reverse; there is no phase.
-/


namespace ShiQIP

open ShiShallow

variable {n : ℕ}

/-- `a ^= c ∧ ¬ s`. -/
def ncaInstrs (c s a : Fin n) (hcs : c ≠ s) (hca : c ≠ a) (hsa : s ≠ a) : List (Instr n) :=
  [.x s] ++ toffoliInstrs c s a hcs hca hsa ++ [.x s]

theorem runLayer_nca (c s a : Fin n) (hcs : c ≠ s) (hca : c ≠ a) (hsa : s ≠ a) (ψ : QState n) :
    runLayer (ncaInstrs c s a hcs hca hsa) ψ =
      fun y => ψ (Function.update y a (xor (y a) (y c && !y s))) := by
  funext y
  rw [ncaInstrs, runLayer_append, runLayer_append]
  change (Instr.x s).apply (runLayer (toffoliInstrs c s a hcs hca hsa) ((Instr.x s).apply ψ)) y = _
  rw [apply_x, runLayer_toffoli, apply_x]
  congr 1
  funext w
  simp only [Function.update_apply]
  have hcs' := hcs.symm; have hca' := hca.symm; have hsa' := hsa.symm
  by_cases h1 : w = s <;> by_cases h2 : w = a <;> simp_all

/-- `t ^= c ∧ (every wire of S reads 0)`. -/
def ztFun (c t : Fin n) (S : List (Fin n)) (y : Bits n) : Bits n :=
  Function.update y t (xor (y t) (y c && S.all fun s => !y s))

/-! ## Description syntax -/

/-- `a ^= c ∧ ¬ s`, as gates. -/
def ncaGates (c s a : ℕ) : List Gate := [.x s] ++ toffoliGates c s a ++ [.x s]

/-- **The zero test**: `t ^= c ∧ (every wire of S reads 0)`, with ancillas `anc`. -/
def ztGates (c t : ℕ) : List ℕ → List ℕ → List Gate
  | [], _ => [.cnot c t]
  | s :: S, a :: anc => ncaGates c s a ++ ztGates a t S anc ++ ncaGates c s a
  | _ :: _, [] => []

theorem filterMap_ncaGates (c s a : Fin n) (hcs : c ≠ s) (hca : c ≠ a) (hsa : s ≠ a) :
    (ncaGates c s a).filterMap (Gate.toInstr? n) = ncaInstrs c s a hcs hca hsa := by
  rw [ncaGates, List.filterMap_append, List.filterMap_append,
    filterMap_toffoliGates c s a hcs hca hsa]
  simp [Gate.toInstr?, ncaInstrs, s.isLt]

set_option linter.unnecessarySeqFocus false in
/-- **The zero test, exactly**, on basis labels with clean ancillas. -/
theorem runLayer_zt : ∀ (S anc : List (Fin n)) (c t : Fin n),
    (c :: t :: (S ++ anc)).Nodup → S.length ≤ anc.length → ∀ (ψ : QState n) (y : Bits n),
      (∀ a ∈ anc, y a = false) →
      runLayer ((ztGates c t (S.map Fin.val) (anc.map Fin.val)).filterMap (Gate.toInstr? n)) ψ y =
        ψ (ztFun c t S y)
  | [], anc, c, t, hnd, _, ψ, y, _ => by
    have hct : c ≠ t := by
      intro h; rw [h] at hnd; simp at hnd
    have h1 : (c : ℕ) ≠ t := fun e => hct (Fin.ext e)
    simp only [List.map_nil, ztGates, List.filterMap_cons, List.filterMap_nil, Gate.toInstr?,
      c.isLt, t.isLt, ne_eq, h1, not_false_eq_true, and_self, dif_pos]
    change (Instr.cnot c t hct).apply ψ y = _
    rw [apply_cnot, cnotFun, ztFun]
    simp
  | s :: S, [], _, _, _, hlen, _, _, _ => by simp at hlen
  | s :: S, a :: anc, c, t, hnd, hlen, ψ, y, hy => by
    have hnd' := hnd
    simp only [List.cons_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or,
      List.nodup_append] at hnd'
    have hcs : c ≠ s := by tauto
    have hca : c ≠ a := by tauto
    have hct : c ≠ t := by tauto
    have hts : t ≠ s := by tauto
    have hta : t ≠ a := by tauto
    have hsa : s ≠ a := by tauto
    have haS : a ∉ S := by tauto
    have hrec : (a :: t :: (S ++ anc)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or, List.nodup_append]
      refine ⟨⟨fun h => hta h.symm, haS, by tauto⟩, ⟨by tauto, by tauto⟩, by tauto, by tauto, ?_⟩
      intro x hx y' hy'
      exact hnd'.2.2.2.2.2 x hx y' (Or.inr hy')
    have hya : y a = false := hy a List.mem_cons_self
    simp only [List.map_cons, ztGates, List.filterMap_append]
    rw [filterMap_ncaGates c s a hcs hca hsa, runLayer_append, runLayer_append, runLayer_nca]
    beta_reduce
    rw [runLayer_zt S anc a t hrec (by simp at hlen; omega) _ _ (fun b hb => by
        rw [Function.update_of_ne (fun e => by rw [e] at hb; tauto)]
        exact hy b (List.mem_cons_of_mem _ hb)),
      runLayer_nca]
    beta_reduce
    congr 1
    funext w
    have hall : (S.all fun s' => !Function.update y a (xor (y a) (y c && !y s)) s') =
        S.all fun s' => !y s' :=
      by
        rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
        refine forall_congr' fun s' => forall_congr' fun hs' => ?_
        have hne : s' ≠ a := fun e => haS (by rw [← e]; exact hs')
        rw [Function.update_of_ne hne]
    simp only [ztFun]
    rw [hall]
    simp only [Function.update_apply, List.all_cons]
    have hct' := hct.symm; have hcs' := hcs.symm; have hca' := hca.symm
    have hts' := hts.symm; have hta' := hta.symm; have hsa' := hsa.symm
    by_cases h1 : w = a <;> by_cases h2 : w = t <;> simp_all <;> cases y c <;> simp

end ShiQIP
