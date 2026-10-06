/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Prefix
import QIP.Bell.Test

/-!
# Q27 — the final block of the Bell test

Block `m + 2` of `bellDesc d` is `CNOT(O' → B)`, `H(O')`, `X(O')`, `X(B)`, then a Toffoli from
`(O', B)` into the new output. If the new output still reads `0`, the acceptance probability is
exactly `bellPr B O' ξ` (**`acceptSum_final`**).
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

variable {d : Desc}

theorem priv_le_totalWires (d : Desc) : d.priv ≤ d.totalWires := by simp [Desc.totalWires]

variable (d) in
/-- The Bell copy wire `B`. -/
def wB : Fin (bellDesc d).totalWires :=
  ⟨bellB d, by rw [totalWires_bellDesc]; have := priv_le_totalWires d; unfold bellB; omega⟩

variable (d) in
/-- The new output wire. -/
def wOut : Fin (bellDesc d).totalWires :=
  ⟨bellOut d, by rw [totalWires_bellDesc]; have := priv_le_totalWires d; unfold bellOut; omega⟩

variable (d) in
/-- The returned wire `O'`. -/
def wO : Fin (bellDesc d).totalWires :=
  ⟨bellO d, by rw [totalWires_bellDesc]; unfold bellO; omega⟩

theorem wO_ne_wB : wO d ≠ wB d := fun h => by
  have := congrArg Fin.val h; have := priv_le_totalWires d
  simp only [wO, wB, bellO, bellB] at *; omega

theorem wO_ne_wOut : wO d ≠ wOut d := fun h => by
  have := congrArg Fin.val h; have := priv_le_totalWires d
  simp only [wO, wOut, bellO, bellOut] at *; omega

theorem wB_ne_wOut : wB d ≠ wOut d := fun h => by
  have := congrArg Fin.val h
  simp only [wB, wOut, bellB, bellOut] at *; omega

variable (d) in
/-- The instructions of the final block. -/
def finalInstrs : List (Instr (bellDesc d).totalWires) :=
  [.cnot (wO d) (wB d) wO_ne_wB, .h (wO d), .x (wO d), .x (wB d)] ++
    toffoliInstrs (wO d) (wB d) (wOut d) wO_ne_wB wO_ne_wOut wB_ne_wOut

theorem blockMat_bell_final : blockMat (bellDesc d) (d.numMsgs + 2) = layerMat (finalInstrs d) := by
  rw [blockMat, blocks_bell_getD (by omega), bellBlock, if_neg (by omega), if_neg (by omega),
    if_neg (by omega), bellFinal, List.filterMap_append,
    show toffoliGates (bellO d) (bellB d) (bellOut d) =
      toffoliGates (wO d) (wB d) (wOut d) from rfl,
    filterMap_toffoliGates _ _ _ wO_ne_wB wO_ne_wOut wB_ne_wOut, finalInstrs]
  have h1 : bellO d < (bellDesc d).totalWires := (wO d).2
  have h2 : bellB d < (bellDesc d).totalWires := (wB d).2
  have h3 : bellO d ≠ bellB d := fun e => wO_ne_wB (Fin.ext e)
  simp [Gate.toInstr?, h1, h2, h3]
  rfl

theorem update_update_comm {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : Qubits n) (a b : Bool) :
    Function.update (Function.update y i a) j b = Function.update (Function.update y j b) i a :=
  Function.update_comm h a b y

/-- **The first four gates of the final block.** -/
theorem run4_apply (ψ : QState (bellDesc d).totalWires) (y : Qubits (bellDesc d).totalWires) :
    runLayer [.cnot (wO d) (wB d) wO_ne_wB, .h (wO d), .x (wO d), .x (wB d)] ψ y =
      hMat (!y (wO d)) false * ψ (Function.update (Function.update y (wB d) (!y (wB d))) (wO d) false) +
        hMat (!y (wO d)) true * ψ (Function.update y (wO d) true) := by
  have hOB := (wO_ne_wB (d := d))
  have hBO := hOB.symm
  simp only [runLayer_cons, runLayer_nil, apply_x, apply_h, apply_cnot, cnotFun,
    Function.update_self, Function.update_of_ne hOB, Function.update_of_ne hBO,
    Function.update_idem]
  congr 2 <;> (congr 1; funext w; simp only [Function.update_apply]; split_ifs <;> simp_all)

theorem runFinal_apply (ψ : QState (bellDesc d).totalWires) (y : Qubits (bellDesc d).totalWires) :
    runLayer (finalInstrs d) ψ y =
      runLayer [.cnot (wO d) (wB d) wO_ne_wB, .h (wO d), .x (wO d), .x (wB d)] ψ
        (Function.update y (wOut d) (xor (y (wOut d)) (y (wO d) && y (wB d)))) := by
  rw [finalInstrs, runLayer_append, runLayer_toffoli]

/-- Wires `out`, `O'`, `B` reset to `0`. -/
def zero3 (y : Qubits (bellDesc d).totalWires) : Qubits (bellDesc d).totalWires :=
  Function.update (Function.update (Function.update y (wOut d) false) (wO d) false) (wB d) false

theorem norm_half_add (a b : ℂ) :
    ‖hMat false false * a + hMat false true * b‖ ^ 2 = ‖a + b‖ ^ 2 / 2 := by
  have hs : hMat false false = ((Real.sqrt 2 : ℂ))⁻¹ := by simp [hMat]
  have ht : hMat false true = ((Real.sqrt 2 : ℂ))⁻¹ := by simp [hMat]
  rw [hs, ht, ← mul_add, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- **The final block, pointwise.** -/
theorem final_term (ψ : QState (bellDesc d).totalWires)
    (hψ : ∀ y, y (wOut d) = true → ψ y = 0) (y : Qubits (bellDesc d).totalWires) :
    (if y (wOut d) = true then ‖runLayer (finalInstrs d) ψ y‖ ^ 2 else 0) =
      if y (wOut d) = true ∧ y (wO d) = true ∧ y (wB d) = true then
        ‖ψ (zero3 y) + ψ (Function.update y (wOut d) false)‖ ^ 2 / 2 else 0 := by
  have hOB := (wO_ne_wB (d := d)); have hBO := hOB.symm
  have hOo := (wO_ne_wOut (d := d)); have hoO := hOo.symm
  have hBo := (wB_ne_wOut (d := d)); have hoB := hBo.symm
  rw [runFinal_apply, run4_apply]
  by_cases hy : y (wOut d) = true
  · by_cases hOB' : y (wO d) = true ∧ y (wB d) = true
    · rw [if_pos hy, if_pos ⟨hy, hOB'⟩, hy, hOB'.1, hOB'.2]
      simp only [Bool.and_self, Bool.xor_true, Bool.not_true, Function.update_of_ne hOo,
        Function.update_of_ne hBo, hOB'.1, hOB'.2, Bool.not_true]
      rw [norm_half_add, show Function.update (Function.update y (wOut d) false) (wO d) true =
        Function.update y (wOut d) false from Function.update_eq_self_iff.mpr
          (by rw [Function.update_of_ne hOo]; exact hOB'.1.symm)]
      unfold zero3
      rw [update_update_comm hBO]
    · rw [if_pos hy, if_neg (fun h => hOB' h.2), hy]
      have hf : (y (wO d) && y (wB d)) = false := by
        cases h1 : y (wO d) <;> cases h2 : y (wB d) <;> simp_all
      rw [hf, Bool.xor_false, show Function.update y (wOut d) true = y from
          Function.update_eq_self_iff.mpr hy.symm,
        hψ _ (by rw [Function.update_of_ne hoO, Function.update_of_ne hoB]; exact hy),
        hψ _ (by rw [Function.update_of_ne hoO]; exact hy)]
      simp
  · rw [if_neg hy, if_neg (fun h => hy h.1)]

/-- **Acceptance after the final block is the Bell probability**, if the new output reads `0`. -/
theorem acceptSum_final {M : Type} [Fintype M] [DecidableEq M]
    (ξ : Qubits (bellDesc d).totalWires × M → ℂ)
    (hξ : ∀ y μ, y (wOut d) = true → ξ (y, μ) = 0) :
    ∑ y, ∑ μ, (if y (wOut d) = true then
      ‖runLayer (finalInstrs d) (fun y' => ξ (y', μ)) y‖ ^ 2 else 0) = bellPr (wB d) (wO d) ξ := by
  have hOB := (wO_ne_wB (d := d)); have hBO := hOB.symm
  have hOo := (wO_ne_wOut (d := d)); have hoO := hOo.symm
  have hBo := (wB_ne_wOut (d := d)); have hoB := hBo.symm
  simp only [fun y μ => final_term (fun y' => ξ (y', μ)) (fun y' h => hξ y' μ h) y]
  rw [bellPr, Finset.sum_comm, Finset.sum_comm (f := fun (z : Z00 (wB d) (wO d)) μ => _)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_filter,
    ← Finset.sum_subtype (Finset.univ.filter fun z : Qubits _ => z (wB d) = false ∧ z (wO d) = false)
      (fun z => by simp) (fun z : Qubits _ =>
        ‖ξ (z, μ) + ξ (Function.update (Function.update z (wO d) true) (wB d) true, μ)‖ ^ 2 / 2)]
  conv_rhs => rw [← Finset.sum_filter_of_ne (p := fun z : Qubits _ => z (wOut d) = false) (by
    intro z _ hz
    by_contra hout
    have hout : z (wOut d) = true := by simpa using hout
    apply hz
    rw [hξ _ _ hout, hξ _ _ (by rw [Function.update_of_ne hoB, Function.update_of_ne hoO]; exact hout)]
    simp), Finset.filter_filter]
  refine Finset.sum_nbij' zero3 (fun z => Function.update (Function.update
      (Function.update z (wOut d) true) (wO d) true) (wB d) true) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    unfold zero3
    simp [Function.update_apply, hOB, hBO, hOo, hoO, hBo, hoB]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    simp [Function.update_apply, hOB, hBO, hOo, hoO, hBo, hoB]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold zero3
    funext w
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    unfold zero3
    funext w
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have key : Function.update (Function.update (zero3 y) (wO d) true) (wB d) true =
        Function.update y (wOut d) false := by
      unfold zero3
      funext w
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    rw [key]

/-! ## Acceptance as a sum -/

theorem kron_one_mulVec_apply {α M : Type} [Fintype α] [Fintype M] [DecidableEq M]
    (A : Matrix α α ℂ) (v : α × M → ℂ) (y : α) (μ : M) :
    ((A ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ v) (y, μ) = (A *ᵥ fun y' => v (y', μ)) y := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem outBit_bell (y : Qubits (bellDesc d).totalWires) :
    outBit (bellDesc d) y ↔ y (wOut d) = true :=
  ⟨fun ⟨_, e⟩ => e, fun e => ⟨(wOut d).2, e⟩⟩

theorem re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **The acceptance expectation of `bellDesc d`, as a sum.** -/
theorem accept_expect_bell {M : Type} [Fintype M] [DecidableEq M]
    (v : Qubits (bellDesc d).totalWires × M → ℂ) :
    (star v ⬝ᵥ (acceptEffect (bellDesc d) M *ᵥ v)).re =
      ∑ y, ∑ μ, if y (wOut d) = true then ‖v (y, μ)‖ ^ 2 else 0 := by
  have hmv : ∀ y μ, (acceptEffect (bellDesc d) M *ᵥ v) (y, μ) =
      if y (wOut d) = true then v (y, μ) else 0 := by
    intro y μ
    rw [acceptEffect, kron_one_mulVec_apply, basisEffect, mulVec_diagonal]
    simp only [outBit_bell]
    split_ifs <;> simp
  rw [dotProduct, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.star_apply, hmv]
  split_ifs
  · exact re_star_mul_self _
  · simp

end ShiQIP
