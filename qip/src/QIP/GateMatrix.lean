/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiShallow_Core
import Quantum.Channel

/-!
# Q16 (groundwork) — matrices of the H/S/T/X/CNOT gates

For the established gate meanings of `ShiShallow` (`Definitions/Def_ShiShallow_Core.lean`, used
unchanged):

* `oneQubitMat U i`: the matrix of `ShiShallow.apply1 U i` on `n` qubits. It is `U ⊗ 1` after
  splitting off wire `i` with `Equiv.funSplitAt` (the wire `i` is the left factor);
  `oneQubitMat_mulVec`: `oneQubitMat U i *ᵥ ψ = ShiShallow.apply1 U i ψ`.
* `cnotMat i j hij`: the permutation matrix of the involution flipping wire `j` by wire `i`;
  `cnotMat_mulVec`: `cnotMat i j hij *ᵥ ψ = ShiShallow.cnotState i j hij ψ`.
* `instrMat g` for `g : ShiShallow.Instr n`, with `instrMat_mulVec : instrMat g *ᵥ ψ = g.apply ψ`.
* Unitarity: `hMat`, `sMat`, `tMat`, `xMat` are unitary, so `instrMat g` is unitary
  (`instrMat_mem_unitaryGroup`). Conjugation by it is therefore a channel
  (`isChannel_instr`).

This is the primitive-gate part of the Q16 bridge; layered circuits and the protocol semantics
of Q15 are not treated here.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder Kronecker

variable {n : ℕ}

/-- Split wire `i` off an `n`-qubit basis state. -/
def splitAt (i : Fin n) : Bits n ≃ Bool × ({ j // j ≠ i } → Bool) := Equiv.funSplitAt i Bool

theorem splitAt_symm_apply (i : Fin n) (x : Bits n) (b : Bool) :
    (splitAt i).symm (b, ((splitAt i) x).2) = Function.update x i b := by
  funext j
  by_cases h : j = i
  · subst h; simp [splitAt, Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [splitAt, Equiv.funSplitAt, Equiv.piSplitAt, h]

/-- The matrix of a one-qubit gate `U` on wire `i`. -/
noncomputable def oneQubitMat (U : Matrix Bool Bool ℂ) (i : Fin n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.reindex (splitAt i).symm (splitAt i).symm (U ⊗ₖ (1 : Matrix ({ j // j ≠ i } → Bool)
    ({ j // j ≠ i } → Bool) ℂ))

theorem oneQubitMat_mulVec (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    oneQubitMat U i *ᵥ ψ = apply1 U i ψ := by
  funext x
  simp only [oneQubitMat, mulVec, dotProduct, reindex_apply, submatrix_apply,
    Equiv.symm_symm, apply1]
  rw [← Equiv.sum_comp (splitAt i).symm]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single ((splitAt i) x).2]
  · simp only [kroneckerMap_apply, one_apply_eq, mul_one, splitAt_symm_apply]
    rfl
  · intro r _ hr
    simp only [kroneckerMap_apply, one_apply_ne (Ne.symm hr), mul_zero, zero_mul]
  · simp

/-- The bit-flip of wire `j` controlled by wire `i`. -/
def cnotFun (i j : Fin n) (x : Bits n) : Bits n := Function.update x j (xor (x j) (x i))

theorem cnotFun_involutive {i j : Fin n} (hij : i ≠ j) : Function.Involutive (cnotFun i j) := by
  intro x
  funext k
  by_cases hk : k = j
  · subst hk; simp [cnotFun, Function.update_of_ne hij]
  · simp [cnotFun, Function.update_of_ne hk]

/-- The CNOT permutation matrix. -/
noncomputable def cnotMat (i j : Fin n) (hij : i ≠ j) : Matrix (Bits n) (Bits n) ℂ :=
  permMat ((cnotFun_involutive hij).toPerm (cnotFun i j))

theorem cnotMat_mulVec (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    cnotMat i j hij *ᵥ ψ = cnotState i j hij ψ := by
  rw [cnotMat, permMat_mulVec]
  funext x
  rfl

/-- The matrix of an instruction. -/
noncomputable def instrMat : Instr n → Matrix (Bits n) (Bits n) ℂ
  | .h i => oneQubitMat hMat i
  | .s i => oneQubitMat sMat i
  | .t i => oneQubitMat tMat i
  | .x i => oneQubitMat xMat i
  | .cnot i j hij => cnotMat i j hij

/-- **The matrices implement the established gate semantics.** -/
theorem instrMat_mulVec (g : Instr n) (ψ : QState n) : instrMat g *ᵥ ψ = g.apply ψ := by
  cases g with
  | h i => exact oneQubitMat_mulVec _ i ψ
  | s i => exact oneQubitMat_mulVec _ i ψ
  | t i => exact oneQubitMat_mulVec _ i ψ
  | x i => exact oneQubitMat_mulVec _ i ψ
  | cnot i j hij => exact cnotMat_mulVec i j hij ψ

/-! ## Unitarity -/

theorem oneQubitMat_mem_unitaryGroup {U : Matrix Bool Bool ℂ} (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (i : Fin n) : oneQubitMat U i ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  have hk : U ⊗ₖ (1 : Matrix ({ j // j ≠ i } → Bool) ({ j // j ≠ i } → Bool) ℂ) ∈
      unitary (Matrix (Bool × ({ j // j ≠ i } → Bool)) (Bool × ({ j // j ≠ i } → Bool)) ℂ) :=
    kronecker_mem_unitary hU (one_mem _)
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  have h2 := Matrix.mem_unitaryGroup_iff'.mp hk
  rw [star_eq_conjTranspose] at h2
  rw [oneQubitMat, reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv, h2,
    submatrix_one_equiv]

theorem cnotMat_mem_unitaryGroup (i j : Fin n) (hij : i ≠ j) :
    cnotMat i j hij ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, cnotMat, permMat_conjTranspose_mul]

theorem sqrtTwo_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem star_sqrtTwo_inv : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem hMat_mem_unitaryGroup : hMat ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  ext a b
  cases a <;> cases b
  all_goals simp [hMat, mul_apply, conjTranspose_apply, sqrtTwo_inv_sq]
  all_goals ring

theorem sMat_mem_unitaryGroup : sMat ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  ext a b
  cases a <;> cases b <;> simp [sMat, mul_apply, conjTranspose_apply]

theorem tPhase_mul : (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) *
    Complex.exp (Complex.I * Real.pi / 4) = 1 := by
  have h : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
  simp

theorem tMat_mem_unitaryGroup : tMat ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  ext a b
  cases a <;> cases b <;> simp [tMat, mul_apply, conjTranspose_apply, tPhase_mul]

theorem xMat_mem_unitaryGroup : xMat ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  ext a b
  cases a <;> cases b <;> simp [xMat, mul_apply, conjTranspose_apply]

/-- **Every instruction acts unitarily.** -/
theorem instrMat_mem_unitaryGroup (g : Instr n) : instrMat g ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  cases g with
  | h i => exact oneQubitMat_mem_unitaryGroup hMat_mem_unitaryGroup i
  | s i => exact oneQubitMat_mem_unitaryGroup sMat_mem_unitaryGroup i
  | t i => exact oneQubitMat_mem_unitaryGroup tMat_mem_unitaryGroup i
  | x i => exact oneQubitMat_mem_unitaryGroup xMat_mem_unitaryGroup i
  | cnot i j hij => exact cnotMat_mem_unitaryGroup i j hij

/-- The density-matrix action of an instruction is a channel. -/
theorem isChannel_instr (g : Instr n) : IsChannel (conjMap (instrMat g)) :=
  isChannel_unitary (instrMat_mem_unitaryGroup g)

/-- On pure states the channel acts by the established state map: `|ψ⟩⟨ψ| ↦ |gψ⟩⟨gψ|`. -/
theorem conjMap_instr_pureState (g : Instr n) (ψ : QState n) :
    conjMap (instrMat g) (pureState ψ) = pureState (g.apply ψ) := by
  rw [conjMap_apply, pureState, ← instrMat_mulVec, mul_vecMulVec, vecMulVec_mul,
    pureState, star_mulVec]

end ShiQIP
