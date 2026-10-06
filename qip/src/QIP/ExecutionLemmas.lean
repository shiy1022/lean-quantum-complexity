/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Classes

/-!
# Q15 — execution lemmas and sanity checks

* `prob_kronecker_one`: an effect that ignores the prover memory sees only the wire marginal of
  a product state.
* `verifierStep_kronecker`: a verifier block acts factor-wise on product states.
* `accept_of_numMsgs_eq_zero`: with no messages, the acceptance probability of **every** prover
  is the pure-state measurement of the block-0 circuit on `|0…0⟩`.
* Examples. For a one-wire, zero-message verifier, the circuit `X 0` accepts every prover with
  probability exactly `1`, and the empty circuit with probability exactly `0`. This checks the
  output convention and the initialization of the wires.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

theorem prob_kronecker_one {α Mem : Type} [Fintype α] [DecidableEq α] [Fintype Mem]
    [DecidableEq Mem] (E ρ : Matrix α α ℂ) {ξ : Matrix Mem Mem ℂ} (hξ : trace ξ = 1) :
    prob (E ⊗ₖ (1 : Matrix Mem Mem ℂ)) (ρ ⊗ₖ ξ) = prob E ρ := by
  rw [prob, ← mul_kronecker_mul, Matrix.one_mul, trace_kronecker, hξ, mul_one, prob]

theorem verifierStep_kronecker (d : Desc) {Mem : Type} [Fintype Mem] [DecidableEq Mem] (j : ℕ)
    (ρ : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) (ξ : Matrix Mem Mem ℂ) :
    verifierStep d Mem j (ρ ⊗ₖ ξ) = conjMap (blockMat d j) ρ ⊗ₖ ξ := by
  rw [verifierStep, conjMap_apply, conjMap_apply, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem conjMap_layer_pureState {n : ℕ} (l : List (Instr n)) (ψ : QState n) :
    conjMap (layerMat l) (pureState ψ) = pureState (runLayer l ψ) := by
  rw [conjMap_apply, pureState, ← layerMat_mulVec, mul_vecMulVec, vecMulVec_mul, pureState,
    star_mulVec]

/-- With no messages, acceptance is the measurement of the block-0 circuit on `|0…0⟩`, for every
prover. -/
theorem accept_of_numMsgs_eq_zero {d : Desc} (h : d.numMsgs = 0) (P : Prover d) :
    accept P = ∑ y, if outBit d y then
      ‖runLayer ((d.blocks.getD 0 []).filterMap (Gate.toInstr? d.totalWires))
        (zeroVec d.totalWires) y‖ ^ 2 else 0 := by
  rw [accept, finalState, h, stateAfterBlock, initState, verifierStep_kronecker, acceptEffect,
    prob_kronecker_one _ _ P.init_density.trace_eq_one, blockMat, conjMap_layer_pureState,
    prob_basisEffect_pureState]

/-! ## Examples -/

/-- One private wire, no messages, block `[X 0]`. -/
def exAlways : Desc := ⟨1, 0, [], [[.x 0]]⟩

/-- One private wire, no messages, no gates. -/
def exNever : Desc := ⟨1, 0, [], [[]]⟩

example : exAlways.Valid ∧ exNever.Valid ∧ exAlways.HasSchedule 0 := by decide

theorem sum_qubits_one (f : Qubits 1 → ℝ) : ∑ y, f y = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool, add_comm]
  rfl

theorem outBit_one {d : Desc} (hd : d.totalWires = 1) (hout : d.out = 0) (y : Qubits d.totalWires) :
    outBit d y ↔ y ⟨0, by omega⟩ = true := by
  constructor
  · rintro ⟨_, h⟩; simpa [hout] using h
  · intro h; exact ⟨by omega, by simpa [hout] using h⟩

/-- **Sanity check**: `X 0` makes every prover accepted with probability one. -/
theorem accept_exAlways (P : Prover exAlways) : accept P = 1 := by
  rw [accept_of_numMsgs_eq_zero rfl]
  simp only [outBit_one (d := exAlways) rfl rfl]
  change (∑ y : Qubits 1, if y 0 = true then
    ‖runLayer [Instr.x (0 : Fin 1)] (zeroVec 1) y‖ ^ 2 else 0) = 1
  refine (sum_qubits_one _).trans ?_
  simp [runLayer, Instr.apply, apply1, xMat, zeroVec, Qubits.zero, funext_iff,
    Function.update_apply, Fin.forall_fin_one]

/-- **Sanity check**: the empty circuit makes every prover accepted with probability zero. -/
theorem accept_exNever (P : Prover exNever) : accept P = 0 := by
  rw [accept_of_numMsgs_eq_zero rfl]
  simp only [outBit_one (d := exNever) rfl rfl]
  change (∑ y : Qubits 1, if y 0 = true then
    ‖runLayer ([] : List (Instr 1)) (zeroVec 1) y‖ ^ 2 else 0) = 0
  refine (sum_qubits_one _).trans ?_
  simp [runLayer, zeroVec, Qubits.zero, funext_iff]

end ShiQIP
