/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.GateMatrix

/-!
# Q16 (partial) — layered circuits as unitary channels

* `layerMat l`, `circuitMat c`: the matrices of a layer and of a layered circuit (later gates
  multiply on the left), built from `instrMat` in the gate order of `ShiShallow.runLayer` and
  `ShiShallow.runLayered`.
* `layerMat_mulVec`, `circuitMat_mulVec`: they implement `runLayer` / `runLayered` exactly.
* `circuitMat_mem_unitaryGroup`: they are unitary, so `conjMap (circuitMat c)` is a channel.
* **Acceptance**: `acceptProb_eq_prob` identifies the existing `ShiShallow.acceptProb` (a sum of
  squared amplitudes) with the measurement probability `prob` of the output-wire effect on the
  density matrix `conjMap (circuitMat c) |x,0⟩⟨x,0|`. The gate set, layer order and output
  convention are unchanged.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow

variable {n : ℕ}

/-- The matrix of a layer: gates applied left to right, so later gates multiply on the left. -/
noncomputable def layerMat (l : List (Instr n)) : Matrix (Bits n) (Bits n) ℂ :=
  l.foldl (fun M g => instrMat g * M) 1

/-- The matrix of a layered circuit. -/
noncomputable def circuitMat (c : Layered n) : Matrix (Bits n) (Bits n) ℂ :=
  c.foldl (fun M l => layerMat l * M) 1

theorem foldl_instrMat_mulVec (l : List (Instr n)) (M : Matrix (Bits n) (Bits n) ℂ)
    (ψ : QState n) :
    (l.foldl (fun M g => instrMat g * M) M) *ᵥ ψ = l.foldl (fun st g => g.apply st) (M *ᵥ ψ) := by
  induction l generalizing M with
  | nil => rfl
  | cons g l ih =>
    simp only [List.foldl_cons]
    rw [ih, ← mulVec_mulVec, instrMat_mulVec]

theorem layerMat_mulVec (l : List (Instr n)) (ψ : QState n) :
    layerMat l *ᵥ ψ = runLayer l ψ := by
  rw [layerMat, foldl_instrMat_mulVec, one_mulVec]; rfl

theorem foldl_layerMat_mulVec (c : Layered n) (M : Matrix (Bits n) (Bits n) ℂ) (ψ : QState n) :
    (c.foldl (fun M l => layerMat l * M) M) *ᵥ ψ = c.foldl (fun st l => runLayer l st) (M *ᵥ ψ) := by
  induction c generalizing M with
  | nil => rfl
  | cons l c ih =>
    simp only [List.foldl_cons]
    rw [ih, ← mulVec_mulVec, layerMat_mulVec]

/-- **The circuit matrix implements `runLayered`.** -/
theorem circuitMat_mulVec (c : Layered n) (ψ : QState n) :
    circuitMat c *ᵥ ψ = runLayered c ψ := by
  rw [circuitMat, foldl_layerMat_mulVec, one_mulVec]; rfl

theorem foldl_instrMat_mem (l : List (Instr n)) {M : Matrix (Bits n) (Bits n) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bits n) ℂ) :
    l.foldl (fun M g => instrMat g * M) M ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  induction l generalizing M with
  | nil => exact hM
  | cons g l ih => exact ih (Submonoid.mul_mem _ (instrMat_mem_unitaryGroup g) hM)

theorem layerMat_mem_unitaryGroup (l : List (Instr n)) :
    layerMat l ∈ Matrix.unitaryGroup (Bits n) ℂ :=
  foldl_instrMat_mem l (Submonoid.one_mem _)

theorem foldl_layerMat_mem (c : Layered n) {M : Matrix (Bits n) (Bits n) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bits n) ℂ) :
    c.foldl (fun M l => layerMat l * M) M ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  induction c generalizing M with
  | nil => exact hM
  | cons l c ih => exact ih (Submonoid.mul_mem _ (layerMat_mem_unitaryGroup l) hM)

/-- **Layered circuits are unitary.** -/
theorem circuitMat_mem_unitaryGroup (c : Layered n) :
    circuitMat c ∈ Matrix.unitaryGroup (Bits n) ℂ :=
  foldl_layerMat_mem c (Submonoid.one_mem _)

theorem isChannel_circuit (c : Layered n) : IsChannel (conjMap (circuitMat c)) :=
  isChannel_unitary (circuitMat_mem_unitaryGroup c)

theorem conjMap_circuit_pureState (c : Layered n) (ψ : QState n) :
    conjMap (circuitMat c) (pureState ψ) = pureState (runLayered c ψ) := by
  rw [conjMap_apply, pureState, ← circuitMat_mulVec, mul_vecMulVec, vecMulVec_mul, pureState,
    star_mulVec]

/-- **Acceptance agrees with the existing amplitude-sum definition.** -/
theorem acceptProb_eq_prob {m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    acceptProb c x out =
      prob (basisEffect fun y : Bits (n + m) => y out = true)
        (conjMap (circuitMat c) (pureState (inputState x))) := by
  rw [conjMap_circuit_pureState, prob_basisEffect_pureState]
  rfl

end ShiQIP
