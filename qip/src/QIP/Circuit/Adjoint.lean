/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.ShiShallowBridge

/-!
# Q28 — exact adjoints of gate lists

The inverse of a circuit is its gate list reversed, each gate replaced by its inverse **within
the gate set** H/S/T/X/CNOT:

  `H⁻¹ = H`, `X⁻¹ = X`, `CNOT⁻¹ = CNOT`, `S⁻¹ = S³`, `T⁻¹ = T⁷`.

* `instrInv`, `adjointInstrs`: the construction on `ShiShallow.Instr`;
  `layerMat_adjointInstrs : layerMat (adjointInstrs l) = (layerMat l)ᴴ`, so
  `runLayer_adjointInstrs : runLayer (adjointInstrs l) (runLayer l ψ) = ψ` exactly, phases
  included.
* `Gate.inv`, `adjointGates`: the same construction on description syntax (`QIP.Syntax`);
  `filterMap_adjointGates` shows it is translated to `adjointInstrs`, and
  `length_adjointGates_le` bounds the expansion by a factor `7`.
* The underlying matrix facts: `sMat ^ 3 = sMatᴴ`, `tMat ^ 7 = tMatᴴ` (through `ω ^ 8 = 1`
  for `ω = exp (iπ/4)`), `hMatᴴ = hMat`, `xMatᴴ = xMat`, `(cnotMat)ᴴ = cnotMat`, and
  `oneQubitMat` is multiplicative in the gate.

This needs only the gate matrices; it does not use any reversible simulation of classical
machines.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

variable {n : ℕ}

/-! ## One-qubit matrix algebra -/

theorem oneQubitMat_mul (U V : Matrix Bool Bool ℂ) (i : Fin n) :
    oneQubitMat U i * oneQubitMat V i = oneQubitMat (U * V) i := by
  rw [oneQubitMat, oneQubitMat, oneQubitMat, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

theorem oneQubitMat_conjTranspose (U : Matrix Bool Bool ℂ) (i : Fin n) :
    (oneQubitMat U i)ᴴ = oneQubitMat Uᴴ i := by
  rw [oneQubitMat, oneQubitMat, reindex_apply, reindex_apply, conjTranspose_submatrix,
    conjTranspose_kronecker, conjTranspose_one]

theorem hMat_conjTranspose : hMatᴴ = hMat := by
  ext a b
  cases a <;> cases b <;> simp [hMat, conjTranspose_apply]

theorem xMat_conjTranspose : xMatᴴ = xMat := by
  ext a b
  cases a <;> cases b <;> simp [xMat, conjTranspose_apply]

theorem sMat_cube : sMat * sMat * sMat = sMatᴴ := by
  ext a b
  cases a <;> cases b <;> simp [sMat, mul_apply, conjTranspose_apply]

/-- The `T` phase `ω = exp (iπ/4)` satisfies `ω ^ 8 = 1`. -/
theorem tPhase_pow_eight : Complex.exp (Complex.I * Real.pi / 4) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  have : (8 : ℕ) * (Complex.I * Real.pi / 4) = 2 * Real.pi * Complex.I := by push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]

theorem tPhase_pow_seven : Complex.exp (Complex.I * Real.pi / 4) ^ 7 =
    (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) := by
  set ω := Complex.exp (Complex.I * Real.pi / 4)
  have h1 : (starRingEnd ℂ) ω * ω = 1 := tPhase_mul
  calc ω ^ 7 = ω ^ 7 * ((starRingEnd ℂ) ω * ω) := by rw [h1, mul_one]
    _ = ω ^ 8 * (starRingEnd ℂ) ω := by ring
    _ = (starRingEnd ℂ) ω := by rw [tPhase_pow_eight, one_mul]

theorem tMat_pow_seven : tMat ^ 7 = tMatᴴ := by
  have hdiag : tMat = diagonal fun a => if a then Complex.exp (Complex.I * Real.pi / 4) else 1 := by
    ext a b; simp [tMat, diagonal_apply]
  rw [hdiag, diagonal_pow, diagonal_conjTranspose]
  congr 1; funext a
  cases a <;> simp [tPhase_pow_seven]

theorem tMat_conjTranspose_eq : tMatᴴ = tMat * tMat * tMat * tMat * tMat * tMat * tMat := by
  rw [← tMat_pow_seven]; simp only [pow_succ, pow_zero, Matrix.one_mul]

/-! ## Inverses of instructions -/

/-- The inverse of an instruction, as a list of instructions of the same gate set. -/
def instrInv : Instr n → List (Instr n)
  | .h i => [.h i]
  | .s i => [.s i, .s i, .s i]
  | .t i => List.replicate 7 (.t i)
  | .x i => [.x i]
  | .cnot i j hij => [.cnot i j hij]

/-- Reverse the list, inverting every instruction. -/
def adjointInstrs (l : List (Instr n)) : List (Instr n) := (l.reverse.map instrInv).flatten

theorem foldl_instrMat_eq (l : List (Instr n)) (M : Matrix (Bits n) (Bits n) ℂ) :
    l.foldl (fun M g => instrMat g * M) M = layerMat l * M := by
  induction l generalizing M with
  | nil => simp [layerMat]
  | cons g l ih =>
    have hc : layerMat (g :: l) = layerMat l * instrMat g := by
      rw [layerMat, List.foldl_cons, ih, Matrix.mul_one]
    rw [List.foldl_cons, ih, hc, Matrix.mul_assoc]

theorem layerMat_cons (g : Instr n) (l : List (Instr n)) :
    layerMat (g :: l) = layerMat l * instrMat g := by
  rw [layerMat, List.foldl_cons, foldl_instrMat_eq, Matrix.mul_one]

theorem layerMat_append (l₁ l₂ : List (Instr n)) :
    layerMat (l₁ ++ l₂) = layerMat l₂ * layerMat l₁ := by
  rw [layerMat, List.foldl_append, foldl_instrMat_eq, foldl_instrMat_eq, Matrix.mul_one]

theorem cnotMat_conjTranspose (i j : Fin n) (hij : i ≠ j) : (cnotMat i j hij)ᴴ = cnotMat i j hij := by
  rw [cnotMat, permMat_conjTranspose, Function.Involutive.toPerm_symm]

theorem layerMat_instrInv (g : Instr n) : layerMat (instrInv g) = (instrMat g)ᴴ := by
  cases g with
  | h i => simp [instrInv, layerMat, instrMat, oneQubitMat_conjTranspose, hMat_conjTranspose]
  | s i =>
    simp only [instrInv, layerMat, List.foldl_cons, List.foldl_nil, instrMat, Matrix.mul_one,
      oneQubitMat_conjTranspose, ← sMat_cube, oneQubitMat_mul]
    simp only [Matrix.mul_assoc]
  | t i =>
    simp only [instrInv, layerMat, List.replicate, List.foldl_cons, List.foldl_nil, instrMat,
      Matrix.mul_one, oneQubitMat_conjTranspose, tMat_conjTranspose_eq, oneQubitMat_mul]
    simp only [Matrix.mul_assoc]
  | x i => simp [instrInv, layerMat, instrMat, oneQubitMat_conjTranspose, xMat_conjTranspose]
  | cnot i j hij => simp [instrInv, layerMat, instrMat, cnotMat_conjTranspose]

/-- **The adjoint list implements the adjoint matrix.** -/
theorem layerMat_adjointInstrs (l : List (Instr n)) :
    layerMat (adjointInstrs l) = (layerMat l)ᴴ := by
  induction l with
  | nil => simp [adjointInstrs, layerMat]
  | cons g l ih =>
    rw [adjointInstrs, List.reverse_cons, List.map_append, List.flatten_append, layerMat_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [layerMat_instrInv, ← adjointInstrs, ih, layerMat_cons, conjTranspose_mul]

/-- **Running the adjoint undoes the circuit**, exactly (phases included). -/
theorem runLayer_adjointInstrs (l : List (Instr n)) (ψ : QState n) :
    runLayer (adjointInstrs l) (runLayer l ψ) = ψ := by
  rw [← layerMat_mulVec, ← layerMat_mulVec, mulVec_mulVec, layerMat_adjointInstrs,
    ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp (layerMat_mem_unitaryGroup l),
    one_mulVec]

theorem length_adjointInstrs_le (l : List (Instr n)) : (adjointInstrs l).length ≤ 7 * l.length := by
  induction l with
  | nil => simp [adjointInstrs]
  | cons g l ih =>
    rw [adjointInstrs, List.reverse_cons, List.map_append, List.flatten_append,
      List.length_append, ← adjointInstrs]
    have : (instrInv g).length ≤ 7 := by cases g <;> simp [instrInv]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_cons]
    omega

/-! ## The same construction on description syntax -/

/-- The inverse of a syntactic gate. -/
def Gate.inv : Gate → List Gate
  | .h i => [.h i]
  | .s i => [.s i, .s i, .s i]
  | .t i => List.replicate 7 (.t i)
  | .x i => [.x i]
  | .cnot i j => [.cnot i j]

/-- Reverse a gate list, inverting every gate. -/
def adjointGates (l : List Gate) : List Gate := (l.reverse.map Gate.inv).flatten

theorem length_adjointGates_le (l : List Gate) : (adjointGates l).length ≤ 7 * l.length := by
  induction l with
  | nil => simp [adjointGates]
  | cons g l ih =>
    rw [adjointGates, List.reverse_cons, List.map_append, List.flatten_append,
      List.length_append, ← adjointGates]
    have : (Gate.inv g).length ≤ 7 := by cases g <;> simp [Gate.inv]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_cons]
    omega

theorem filterMap_inv (g : Gate) :
    (Gate.inv g).filterMap (Gate.toInstr? n) = ((Gate.toInstr? n g).map instrInv).getD [] := by
  cases g with
  | h i => by_cases hi : i < n <;> simp [Gate.inv, Gate.toInstr?, instrInv, hi]
  | s i => by_cases hi : i < n <;> simp [Gate.inv, Gate.toInstr?, instrInv, hi]
  | t i => by_cases hi : i < n <;> simp [Gate.inv, Gate.toInstr?, instrInv, hi, List.replicate]
  | x i => by_cases hi : i < n <;> simp [Gate.inv, Gate.toInstr?, instrInv, hi]
  | cnot i j =>
    by_cases h : i < n ∧ j < n ∧ i ≠ j
    · simp [Gate.inv, Gate.toInstr?, instrInv, h]
    · simp only [Gate.inv, Gate.toInstr?, dif_neg h, List.filterMap_cons, List.filterMap_nil,
        Option.map_none, Option.getD_none]

/-- The syntactic adjoint of an in-range gate list translates to the instruction adjoint. -/
theorem filterMap_adjointGates (l : List Gate) (hl : ∀ g ∈ l, (Gate.toInstr? n g).isSome) :
    (adjointGates l).filterMap (Gate.toInstr? n) = adjointInstrs (l.filterMap (Gate.toInstr? n)) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    obtain ⟨g', hg'⟩ := Option.isSome_iff_exists.mp (hl g List.mem_cons_self)
    rw [adjointGates, List.reverse_cons, List.map_append, List.flatten_append,
      List.filterMap_append, ← adjointGates, ih fun g h => hl g (List.mem_cons_of_mem _ h),
      List.filterMap_cons, hg']
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      filterMap_inv, hg', Option.map_some, Option.getD_some, adjointInstrs, List.reverse_cons,
      List.map_append, List.flatten_append]

end ShiQIP
