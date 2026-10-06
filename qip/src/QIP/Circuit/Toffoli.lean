/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Circuit.Control

/-!
# Q28 — an exact Toffoli template in H/S/T/X/CNOT

* `cczInstrs a b c`: 13 CNOT/T gates (`T† = T⁷`). On basis label `(a, b, c)` the accumulated
  phase exponent is `(a⊕b⊕c) + 7(b⊕c) + 7(a⊕c) + a + b + c + 7(a⊕b) ≡ 4abc (mod 8)`, so
  `runLayer_ccz` holds exactly: the circuit multiplies by `(-1)^{abc}`, with no global phase.
  The only facts used about `ω = exp (iπ/4)` are `ω ^ 8 = 1` and `ω ^ 4 = -1`.
* `toffoliInstrs a b c = H_c · CCZ · H_c` (33 instructions); `runLayer_toffoli`:
  `ψ ↦ (y ↦ ψ (y with wire c xored by (y a && y b)))`, exactly. The control wires `a`, `b` are
  never changed (`toffoli_controls_preserved`).
* `toffoliGates`: the same circuit as description syntax, translated exactly
  (`filterMap_toffoliGates`), with `33` gates.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow

theorem update_of_eq {n : ℕ} {f : Bits n} {a : Fin n} {b : Bool} (h : f a = b) :
    Function.update f a b = f := by rw [← h]; exact Function.update_eq_self a f

theorem apply_t {n : ℕ} (i : Fin n) (ψ : QState n) (y : Bits n) :
    (Instr.t i).apply ψ y = (if y i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ y := by
  simp only [Instr.apply, apply1, Fintype.sum_bool, tMat, of_apply]
  cases h : y i <;> simp [update_of_eq h]

theorem tPhase_pow_four : Complex.exp (Complex.I * Real.pi / 4) ^ 4 = -1 := by
  rw [← Complex.exp_nat_mul]
  have : ((4 : ℕ) : ℂ) * (Complex.I * Real.pi / 4) = Real.pi * Complex.I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

theorem pow_eq_pow_mod_eight {w : ℂ} (h : w ^ 8 = 1) (k : ℕ) : w ^ k = w ^ (k % 8) := by
  conv_lhs => rw [← Nat.div_add_mod k 8, pow_add, pow_mul, h, one_pow, one_mul]

def tdg {n : ℕ} (w : Fin n) : List (Instr n) := List.replicate 7 (.t w)

def cczInstrs {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : List (Instr n) :=
  [.cnot b c hbc] ++ tdg c ++ [.cnot a c hac, .t c, .cnot b c hbc] ++ tdg c ++
    [.cnot a c hac, .t b, .t c, .cnot a b hab, .t a] ++ tdg b ++ [.cnot a b hab]

theorem runLayer_ccz {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ψ : QState n) (y : Bits n) :
    runLayer (cczInstrs a b c hab hac hbc) ψ y =
      (if y a && y b && y c then -1 else 1) * ψ y := by
  have hba := hab.symm; have hca := hac.symm; have hcb := hbc.symm
  simp only [cczInstrs, tdg, List.replicate, List.cons_append, List.nil_append, runLayer,
    List.foldl_cons, List.foldl_nil]
  simp only [apply_t, apply_cnot, cnotFun, Function.update_apply, if_neg hab, if_neg hac,
    if_neg hbc, if_neg hcb, if_true]
  have h8 := tPhase_pow_eight
  have h4 := tPhase_pow_four
  generalize Complex.exp (Complex.I * Real.pi / 4) = w at h8 h4 ⊢
  cases ha : y a <;> cases hb : y b <;> cases hc : y c <;>
    simp [hb, hc, update_of_eq] <;> ring_nf <;> rw [pow_eq_pow_mod_eight h8] <;> norm_num [h4]

theorem apply_h {n : ℕ} (i : Fin n) (ψ : QState n) (y : Bits n) :
    (Instr.h i).apply ψ y = hMat (y i) false * ψ (Function.update y i false) +
      hMat (y i) true * ψ (Function.update y i true) := by
  simp only [Instr.apply, apply1, Fintype.sum_bool]; ring

def toffoliInstrs {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    List (Instr n) := [.h c] ++ cczInstrs a b c hab hac hbc ++ [.h c]

theorem runLayer_toffoli {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ψ : QState n) (y : Bits n) :
    runLayer (toffoliInstrs a b c hab hac hbc) ψ y =
      ψ (Function.update y c (xor (y c) (y a && y b))) := by
  rw [toffoliInstrs, runLayer_append, runLayer_append]
  change (Instr.h c).apply (runLayer (cczInstrs a b c hab hac hbc) ((Instr.h c).apply ψ)) y = _
  simp only [apply_h, runLayer_ccz, Function.update_self, Function.update_idem,
    Function.update_of_ne hac, Function.update_of_ne hbc]
  have hq : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1 / 2 := by rw [sq]; exact sqrtTwo_inv_sq
  cases ha : y a <;> cases hb : y b <;> cases hc : y c <;>
    simp [hc, hMat, update_of_eq] <;> ring_nf <;> rw [hq] <;> ring

/-- The Toffoli permutation leaves the control wires unchanged. -/
theorem toffoli_controls_preserved {n : ℕ} {a b c : Fin n} (hac : a ≠ c) (hbc : b ≠ c)
    (y : Bits n) (v : Bool) :
    Function.update y c v a = y a ∧ Function.update y c v b = y b :=
  ⟨Function.update_of_ne hac _ _, Function.update_of_ne hbc _ _⟩

/-! ## Description syntax -/

def tdgGates (w : ℕ) : List Gate := List.replicate 7 (.t w)

def cczGates (a b c : ℕ) : List Gate :=
  [.cnot b c] ++ tdgGates c ++ [.cnot a c, .t c, .cnot b c] ++ tdgGates c ++
    [.cnot a c, .t b, .t c, .cnot a b, .t a] ++ tdgGates b ++ [.cnot a b]

def toffoliGates (a b c : ℕ) : List Gate := [.h c] ++ cczGates a b c ++ [.h c]

theorem length_toffoliGates (a b c : ℕ) : (toffoliGates a b c).length = 33 := by
  simp [toffoliGates, cczGates, tdgGates]

theorem filterMap_toffoliGates {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (toffoliGates a b c).filterMap (Gate.toInstr? n) = toffoliInstrs a b c hab hac hbc := by
  have h1 : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  have h2 : (a : ℕ) ≠ c := fun e => hac (Fin.ext e)
  have h3 : (b : ℕ) ≠ c := fun e => hbc (Fin.ext e)
  simp [toffoliGates, toffoliInstrs, cczGates, cczInstrs, tdgGates, tdg, Gate.toInstr?, a.isLt,
    b.isLt, c.isLt, h1, h2, h3, List.replicate]

end ShiQIP
