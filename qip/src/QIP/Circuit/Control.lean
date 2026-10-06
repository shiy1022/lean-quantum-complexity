/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Circuit.Adjoint

/-!
# Q28 — swap macro

`swapInstrs i j` is the three-CNOT circuit `CNOT(i,j) CNOT(j,i) CNOT(i,j)`. It exchanges wires
`i` and `j` exactly (`runLayer_swapInstrs`: `ψ ↦ ψ ∘ swap`), with no phase. Its matrix is the
permutation matrix of the wire swap (`layerMat_swapInstrs`), and the description-level version
uses three gates (`swapGates`).

Controlled-gate templates (Toffoli) and the all-pass test are not yet formalized here.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow

variable {n : ℕ}

/-- The CNOT action on basis labels. -/
theorem apply_cnot (i j : Fin n) (hij : i ≠ j) (ψ : QState n) (y : Bits n) :
    (Instr.cnot i j hij).apply ψ y = ψ (cnotFun i j y) := rfl

/-- `CNOT(i,j) CNOT(j,i) CNOT(i,j)`. -/
def swapInstrs (i j : Fin n) (hij : i ≠ j) : List (Instr n) :=
  [.cnot i j hij, .cnot j i (Ne.symm hij), .cnot i j hij]

theorem cnot_cnot_cnot (i j : Fin n) (hij : i ≠ j) (y : Bits n) :
    cnotFun i j (cnotFun j i (cnotFun i j y)) = y ∘ Equiv.swap i j := by
  funext k
  have hji : j ≠ i := Ne.symm hij
  by_cases hki : k = i
  · subst hki
    simp only [cnotFun, Function.comp_apply, Equiv.swap_apply_left, Function.update_self,
      Function.update_of_ne hij]
    cases y k <;> cases y j <;> rfl
  · by_cases hkj : k = j
    · subst hkj
      simp only [cnotFun, Function.comp_apply, Equiv.swap_apply_right, Function.update_self,
        Function.update_of_ne hji, Function.update_of_ne hij]
      cases y i <;> cases y k <;> rfl
    · simp [cnotFun, Function.update_of_ne hki, Function.update_of_ne hkj,
        Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- **The swap macro exchanges two wires exactly.** -/
theorem runLayer_swapInstrs (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    runLayer (swapInstrs i j hij) ψ = fun y => ψ (y ∘ Equiv.swap i j) := by
  funext y
  change ψ (cnotFun i j (cnotFun j i (cnotFun i j y))) = _
  rw [cnot_cnot_cnot i j hij]

theorem swapInstrs_mulVec (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    layerMat (swapInstrs i j hij) *ᵥ ψ = fun y => ψ (y ∘ Equiv.swap i j) := by
  rw [layerMat_mulVec, runLayer_swapInstrs]

/-- The three-gate swap on description syntax. -/
def swapGates (i j : ℕ) : List Gate := [.cnot i j, .cnot j i, .cnot i j]

theorem filterMap_swapGates (i j : Fin n) (hij : i ≠ j) :
    (swapGates i j).filterMap (Gate.toInstr? n) = swapInstrs i j hij := by
  have h1 : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
  simp [swapGates, swapInstrs, Gate.toInstr?, i.isLt, j.isLt, h1, Ne.symm h1]

end ShiQIP
