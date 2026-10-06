/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.SDP.Reindex

/-!
# Q25 (abstract part) — testers of parallel verifiers

A verifier description `d` is the **parallel composition** of `d₁` and `d₂` (with the same
number of messages) when the data of `PairData d₁ d₂ d` is given:

* a wire bijection `σ : Qubits W ≃ (Qubits W₁ × Qubits W₂) × Bool`, with one fresh ancilla wire;
* register bijections `τ j : Reg d j ≃ Reg d₁ j × Reg d₂ j`, compatible with σ: reading register
  `j` and replacing its content commute with `σ` (`reg_read`, `reg_write`);
* the initial all-zero vector corresponds to the all-zero vectors and ancilla `0`;
* every block is the tensor product of the two blocks (`block_prod`, for `j < m`), and the last
  block is the tensor product followed by a gate `F` (`block_last`);
* `F` turns the accepting effect into `E₁ ⊗ E₂` on the clean ancilla (`final_effect`).

**`tester_pairData`**: the tester of `d` is the product tester `prodMat (tester d₁) (tester d₂)`,
relabelled along `τ`. **`value_pairData`**: `value d = value d₁ * value d₂` against
**arbitrary** provers of `d`, entangled across the two copies.

The proof tracks the transition matrices as tensor products (`tens`): `transfer_tens` for prover
turns and `mul_tens` for blocks.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Tensor products of transition matrices -/

section Tens

variable {V V₁ V₂ H H₁ H₂ : Type}

/-- The tensor product of two transition matrices and an ancilla vector, along wire and history
bijections. -/
def tens (σ : V ≃ (V₁ × V₂) × Bool) (hE : H ≃ H₁ × H₂) (A₁ : Matrix V₁ H₁ ℂ)
    (A₂ : Matrix V₂ H₂ ℂ) (a : Bool → ℂ) : Matrix V H ℂ :=
  Matrix.of fun w h => A₁ (σ w).1.1 (hE h).1 * A₂ (σ w).1.2 (hE h).2 * a (σ w).2

/-- Histories of one more turn. -/
def histStep {G G₁ G₂ : Type} (hE : H ≃ H₁ × H₂) (τ : G ≃ G₁ × G₂) :
    (H × G) × G ≃ ((H₁ × G₁) × G₁) × ((H₂ × G₂) × G₂) :=
  ((hE.prodCongr τ).trans (Equiv.prodProdProdComm _ _ _ _)).prodCongr τ |>.trans
    (Equiv.prodProdProdComm _ _ _ _)

theorem histStep_apply {G G₁ G₂ : Type} (hE : H ≃ H₁ × H₂) (τ : G ≃ G₁ × G₂) (h : H) (x y : G) :
    histStep hE τ ((h, x), y) =
      ((((hE h).1, (τ x).1), (τ y).1), (((hE h).2, (τ x).2), (τ y).2)) := rfl

variable {R R₁ R₂ G G₁ G₂ : Type} [DecidableEq G] [DecidableEq G₁] [DecidableEq G₂]

/-- **Prover turns tensor.** -/
theorem transfer_tens (σ : V ≃ (V₁ × V₂) × Bool) (hE : H ≃ H₁ × H₂) (τ : G ≃ G₁ × G₂)
    (e : V ≃ R × G) (e₁ : V₁ ≃ R₁ × G₁) (e₂ : V₂ ≃ R₂ × G₂)
    (hread : ∀ w, τ (e w).2 = ((e₁ (σ w).1.1).2, (e₂ (σ w).1.2).2))
    (hwrite : ∀ w x, σ (e.symm ((e w).1, x)) =
      ((e₁.symm ((e₁ (σ w).1.1).1, (τ x).1), e₂.symm ((e₂ (σ w).1.2).1, (τ x).2)), (σ w).2))
    (A₁ : Matrix V₁ H₁ ℂ) (A₂ : Matrix V₂ H₂ ℂ) (a : Bool → ℂ) :
    transfer e (tens σ hE A₁ A₂ a) =
      tens σ (histStep hE τ) (transfer e₁ A₁) (transfer e₂ A₂) a := by
  ext w ⟨⟨h, x⟩, y⟩
  simp only [transfer, tens, of_apply, histStep_apply, hwrite]
  have hy : ((e w).2 = y) ↔ ((e₁ (σ w).1.1).2 = (τ y).1 ∧ (e₂ (σ w).1.2).2 = (τ y).2) := by
    rw [← Prod.mk.injEq, ← hread, τ.apply_eq_iff_eq]
  by_cases h1 : (e₁ (σ w).1.1).2 = (τ y).1 <;> by_cases h2 : (e₂ (σ w).1.2).2 = (τ y).2 <;>
    simp [h1, h2, hy]

variable [Fintype V₁] [Fintype V₂] [Fintype V] [DecidableEq V₁] [DecidableEq V₂]

/-- The tensor product of two block unitaries, along `σ`, with the identity on the ancilla. -/
def blockTens (σ : V ≃ (V₁ × V₂) × Bool) (B₁ : Matrix V₁ V₁ ℂ) (B₂ : Matrix V₂ V₂ ℂ) :
    Matrix V V ℂ :=
  ((B₁ ⊗ₖ B₂) ⊗ₖ (1 : Matrix Bool Bool ℂ)).submatrix σ σ

/-- **Blocks tensor.** -/
theorem mul_tens (σ : V ≃ (V₁ × V₂) × Bool) (hE : H ≃ H₁ × H₂) (B₁ : Matrix V₁ V₁ ℂ)
    (B₂ : Matrix V₂ V₂ ℂ) (A₁ : Matrix V₁ H₁ ℂ) (A₂ : Matrix V₂ H₂ ℂ) (a : Bool → ℂ) :
    blockTens σ B₁ B₂ * tens σ hE A₁ A₂ a = tens σ hE (B₁ * A₁) (B₂ * A₂) a := by
  ext w h
  simp only [blockTens, tens, mul_apply, submatrix_apply, kroneckerMap_apply, of_apply,
    one_apply]
  rw [σ.sum_comp (fun p => (B₁ (σ w).1.1 p.1.1 * B₂ (σ w).1.2 p.1.2 *
      if (σ w).2 = p.2 then (1 : ℂ) else 0) * (A₁ p.1.1 (hE h).1 * A₂ p.1.2 (hE h).2 * a p.2))]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases (σ w).2 <;> simp <;> ring

theorem sum_split (σ : V ≃ (V₁ × V₂) × Bool) (F : V → ℂ) :
    ∑ w, F w = ∑ a, ∑ b, (F (σ.symm ((a, b), false)) + F (σ.symm ((a, b), true))) := by
  rw [← σ.symm.sum_comp F]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => add_comm _ _

/-- The ancilla vector `|0⟩`. -/
def ancZero : Bool → ℂ := fun b => if b then 0 else 1

/-- **Conjugating an effect by a tensor product** with clean ancilla. -/
theorem tens_conj (σ : V ≃ (V₁ × V₂) × Bool) (hE : H ≃ H₁ × H₂) (A₁ : Matrix V₁ H₁ ℂ)
    (A₂ : Matrix V₂ H₂ ℂ) (G : Matrix V V ℂ) (E₁ : Matrix V₁ V₁ ℂ) (E₂ : Matrix V₂ V₂ ℂ)
    (hG : ∀ p p' : V₁ × V₂, G (σ.symm (p, false)) (σ.symm (p', false)) = E₁ p.1 p'.1 * E₂ p.2 p'.2) :
    (tens σ hE A₁ A₂ ancZero)ᴴ * G * tens σ hE A₁ A₂ ancZero =
      ((A₁ᴴ * E₁ * A₁) ⊗ₖ (A₂ᴴ * E₂ * A₂)).submatrix hE hE := by
  ext x x'
  simp only [mul_apply, conjTranspose_apply, submatrix_apply, kroneckerMap_apply]
  simp only [sum_split σ]
  simp only [tens, of_apply, Equiv.apply_symm_apply, ancZero, Bool.false_eq_true, ↓reduceIte,
    star_zero, mul_zero, zero_mul, add_zero, mul_one, hG]
  simp only [Finset.sum_mul, Finset.mul_sum, star_mul']
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  conv_lhs => rw [Finset.sum_congr rfl fun a' _ => Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

end Tens

theorem tens_congr {V V₁ V₂ H H₁ H₂ : Type} {σ : V ≃ (V₁ × V₂) × Bool} {hE hE' : H ≃ H₁ × H₂} (h : ∀ x, hE x = hE' x)
    (A₁ : Matrix V₁ H₁ ℂ) (A₂ : Matrix V₂ H₂ ℂ) (a : Bool → ℂ) :
    tens σ hE A₁ A₂ a = tens σ hE' A₁ A₂ a := by
  ext w x; simp [tens, h]

/-! ## Parallel composition of descriptions -/

/-- The tester of `d` at turn `k`: `A_kᴴ E A_k`. -/
noncomputable def testerAt (d : Desc) (k : ℕ) :
    Matrix (Hist (Reg d) (Reg d) k) (Hist (Reg d) (Reg d) k) ℂ :=
  (transMat d k)ᴴ * basisEffect (outBit d) * transMat d k

theorem testerAt_posSemidef (d : Desc) (k : ℕ) : (testerAt d k).PosSemidef :=
  (isEffect_basisEffect (outBit d)).posSemidef.conjTranspose_mul_mul_same _

theorem value_eq_sdpVal_testerAt (d : Desc) {k : ℕ} (hk : d.numMsgs = k) :
    value d = sdpVal (testerAt d k) := by
  subst hk; exact value_eq_sdpVal d

/-- **Parallel composition data**: `d` runs `d₁` and `d₂` side by side on `m` messages, with one
fresh ancilla, and its last block ends with a gate `F` combining the two outputs. -/
structure PairData (d₁ d₂ d : Desc) where
  σ : Qubits d.totalWires ≃ (Qubits d₁.totalWires × Qubits d₂.totalWires) × Bool
  τ : ∀ j, Reg d j ≃ Reg d₁ j × Reg d₂ j
  reg_read : ∀ j w, τ j (wireSplitE d j w).2 =
    ((wireSplitE d₁ j (σ w).1.1).2, (wireSplitE d₂ j (σ w).1.2).2)
  reg_write : ∀ j w x, σ ((wireSplitE d j).symm ((wireSplitE d j w).1, x)) =
    (((wireSplitE d₁ j).symm ((wireSplitE d₁ j (σ w).1.1).1, (τ j x).1),
      (wireSplitE d₂ j).symm ((wireSplitE d₂ j (σ w).1.2).1, (τ j x).2)), (σ w).2)
  zero : ∀ w, zeroVec d.totalWires w =
    zeroVec d₁.totalWires (σ w).1.1 * zeroVec d₂.totalWires (σ w).1.2 * ancZero (σ w).2
  block_prod : ∀ j < d.numMsgs, blockMat d j = blockTens σ (blockMat d₁ j) (blockMat d₂ j)
  F : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ
  block_last : blockMat d d.numMsgs =
    F * blockTens σ (blockMat d₁ d.numMsgs) (blockMat d₂ d.numMsgs)
  final_effect : ∀ w w', (σ w).2 = false → (σ w').2 = false →
    (Fᴴ * basisEffect (outBit d) * F) w w' =
      basisEffect (outBit d₁) (σ w).1.1 (σ w').1.1 * basisEffect (outBit d₂) (σ w).1.2 (σ w').1.2

namespace PairData

variable {d₁ d₂ d : Desc} (D : PairData d₁ d₂ d)

/-- Joint histories of `d` as pairs of histories of `d₁` and `d₂`. -/
def hE (k : ℕ) : Hist (Reg d) (Reg d) k ≃ Hist (Reg d₁) (Reg d₁) k × Hist (Reg d₂) (Reg d₂) k :=
  (histMap D.τ D.τ k).trans (histEquiv (Reg d₁) (Reg d₁) (Reg d₂) (Reg d₂) k)

theorem hE_succ (k : ℕ) (x : Hist (Reg d) (Reg d) (k + 1)) :
    D.hE (k + 1) x = histStep (D.hE k) (D.τ k) x := rfl

/-- The zero column. -/
def zeroCol (e : Desc) : Matrix (Qubits e.totalWires) (Hist (Reg e) (Reg e) 0) ℂ :=
  Matrix.of fun w _ => zeroVec e.totalWires w

theorem transMat_zero (e : Desc) : transMat e 0 = blockMat e 0 * zeroCol e := by
  ext w u; simp [transMat, zeroCol, mul_apply, mulVec, dotProduct]

theorem zeroCol_tens (hE0 : Hist (Reg d) (Reg d) 0 ≃ Hist (Reg d₁) (Reg d₁) 0 ×
    Hist (Reg d₂) (Reg d₂) 0) :
    zeroCol d = tens D.σ hE0 (zeroCol d₁) (zeroCol d₂) ancZero := by
  ext w u; simp [zeroCol, tens, D.zero]

/-- **Transition matrices of the parallel composition**: before the last block they are tensor
products. -/
theorem transMat_eq : ∀ k < d.numMsgs, transMat d k =
    tens D.σ (D.hE k) (transMat d₁ k) (transMat d₂ k) ancZero
  | 0, h => by
    rw [transMat_zero, transMat_zero, transMat_zero, D.block_prod 0 h, D.zeroCol_tens (D.hE 0),
      mul_tens]
  | k + 1, h => by
    change blockMat d (k + 1) * transfer (wireSplitE d k) (transMat d k) =
      tens D.σ (D.hE (k + 1)) (blockMat d₁ (k + 1) * transfer (wireSplitE d₁ k) (transMat d₁ k))
        (blockMat d₂ (k + 1) * transfer (wireSplitE d₂ k) (transMat d₂ k)) ancZero
    rw [transMat_eq k (by omega), transfer_tens D.σ (D.hE k) (D.τ k) _ _ _ (D.reg_read k)
      (D.reg_write k), D.block_prod (k + 1) h, mul_tens]
    exact tens_congr (fun x => (D.hE_succ k x).symm) _ _ _

/-- The last transition matrix: the gate `F` after a tensor product. -/
theorem transMat_last : transMat d d.numMsgs =
    D.F * tens D.σ (D.hE d.numMsgs) (transMat d₁ d.numMsgs) (transMat d₂ d.numMsgs) ancZero := by
  have e : ∀ k, k = d.numMsgs → transMat d k =
      D.F * tens D.σ (D.hE k) (transMat d₁ k) (transMat d₂ k) ancZero := by
    intro k hk
    have hb := D.block_last
    rw [← hk] at hb
    cases k with
    | zero =>
      rw [transMat_zero, transMat_zero, transMat_zero, hb, D.zeroCol_tens (D.hE 0),
        Matrix.mul_assoc, mul_tens]
    | succ k =>
      change blockMat d (k + 1) * transfer (wireSplitE d k) (transMat d k) =
        D.F * tens D.σ (D.hE (k + 1))
          (blockMat d₁ (k + 1) * transfer (wireSplitE d₁ k) (transMat d₁ k))
          (blockMat d₂ (k + 1) * transfer (wireSplitE d₂ k) (transMat d₂ k)) ancZero
      rw [D.transMat_eq k (by omega), transfer_tens D.σ (D.hE k) (D.τ k) _ _ _ (D.reg_read k)
        (D.reg_write k), hb, Matrix.mul_assoc, mul_tens]
      exact congrArg _ (tens_congr (fun x => (D.hE_succ k x).symm) _ _ _)
  exact e _ rfl

/-- **The tester of the parallel composition is the relabelled product tester.** -/
theorem tester_eq : tester d =
    (prodMat (testerAt d₁ d.numMsgs) (testerAt d₂ d.numMsgs)).submatrix
      (histMap D.τ D.τ d.numMsgs) (histMap D.τ D.τ d.numMsgs) := by
  have hT : tester d = (tens D.σ (D.hE d.numMsgs) (transMat d₁ d.numMsgs) (transMat d₂ d.numMsgs)
      ancZero)ᴴ * (D.Fᴴ * basisEffect (outBit d) * D.F) *
        tens D.σ (D.hE d.numMsgs) (transMat d₁ d.numMsgs) (transMat d₂ d.numMsgs) ancZero := by
    rw [tester, D.transMat_last, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hT, tens_conj D.σ (D.hE d.numMsgs) _ _ _ (basisEffect (outBit d₁)) (basisEffect (outBit d₂))
    (fun p p' => by
      have := D.final_effect (D.σ.symm (p, false)) (D.σ.symm (p', false)) (by simp) (by simp)
      simpa using this)]
  ext x x'
  rfl

include D in
/-- **The product theorem for parallel compositions**, against arbitrary provers. -/
theorem value_eq (h₁ : d₁.numMsgs = d.numMsgs) (h₂ : d₂.numMsgs = d.numMsgs) :
    value d = value d₁ * value d₂ := by
  rw [value_eq_sdpVal, tester_eq D,
    sdpVal_relabel D.τ D.τ (prodMat_posSemidef (testerAt_posSemidef _ _) (testerAt_posSemidef _ _)),
    sdpVal_prod (testerAt_posSemidef _ _) (testerAt_posSemidef _ _),
    ← value_eq_sdpVal_testerAt d₁ h₁, ← value_eq_sdpVal_testerAt d₂ h₂]

end PairData

end ShiQIP
