/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Marginal
import Quantum.BellBound

/-!
# Q27 — the Bell test on two wires of a global vector

For distinct wires `b`, `o` and a vector `ξ` on the wires and a memory:

* `bellPr b o ξ`: the probability of finding `(b, o)` in `|Φ⁺⟩`;
* `margB b ξ`: the reduced state of wire `b`;
* **`bellPr_le`**: `bellPr ≤ F(margB, I/2)²` (from `bell_prob_le`);
* `margB_eq_reduceTo`: `margB` is `reduceTo` on the one-wire embedding.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {W : ℕ} {M : Type} [Fintype M] [DecidableEq M]

/-- Basis labels with wires `b` and `o` at `0`. -/
abbrev Z00 (b o : Fin W) : Type := {z : Qubits W // z b = false ∧ z o = false}

/-- Basis labels with wire `b` at `0`. -/
abbrev Z0 (b : Fin W) : Type := {z : Qubits W // z b = false}

/-- The probability of finding wires `(b, o)` in `|Φ⁺⟩`. -/
noncomputable def bellPr (b o : Fin W) (ξ : Qubits W × M → ℂ) : ℝ :=
  ∑ z : Z00 b o, ∑ μ : M,
    ‖ξ (z.1, μ) + ξ (Function.update (Function.update z.1 o true) b true, μ)‖ ^ 2 / 2

/-- The reduced state of wire `b`. -/
noncomputable def margB (b : Fin W) (ξ : Qubits W × M → ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun x x' => ∑ z : Z0 b, ∑ μ : M,
    ξ (Function.update z.1 b x, μ) * star (ξ (Function.update z.1 b x', μ))

theorem re_mul_star_half (x : ℂ) : (x * star x / 2).re = ‖x‖ ^ 2 / 2 := by
  rw [Complex.div_ofNat_re, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem trace_bell_pureState {R : Type} [Fintype R] [DecidableEq R] (φ : (Bool × Bool) × R → ℂ) :
    (trace ((pureState bellVecB ⊗ₖ (1 : Matrix R R ℂ)) * pureState φ)).re =
      ∑ r, ‖φ ((false, false), r) + φ ((true, true), r)‖ ^ 2 / 2 := by
  have hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have key : trace ((pureState bellVecB ⊗ₖ (1 : Matrix R R ℂ)) * pureState φ) =
      ∑ r, (φ ((false, false), r) + φ ((true, true), r)) *
        star (φ ((false, false), r) + φ ((true, true), r)) / 2 := by
    simp only [trace, diag_apply, mul_apply, kroneckerMap_apply, one_apply, pureState,
      vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Fintype.sum_bool, bellVecB,
      Bool.true_eq_false, Bool.false_eq_true, if_false, star_zero, add_zero, zero_add, hs]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [star_add]
    linear_combination (φ ((false, false), r) + φ ((true, true), r)) *
      (star (φ ((false, false), r)) + star (φ ((true, true), r))) * sqrtTwo_inv_mul_self
  rw [key, Complex.re_sum]
  exact Finset.sum_congr rfl fun r _ => re_mul_star_half _

/-- `Bool × Z00 b o ≃ Z0 b`: put back the value of wire `o`. -/
def splitO (b o : Fin W) (hbo : b ≠ o) : Bool × Z00 b o ≃ Z0 b where
  toFun p := ⟨Function.update p.2.1 o p.1, by rw [Function.update_of_ne hbo]; exact p.2.2.1⟩
  invFun z := (z.1 o, ⟨Function.update z.1 o false,
    by rw [Function.update_of_ne hbo]; exact z.2, Function.update_self _ _ _⟩)
  left_inv p := by
    obtain ⟨y, z, hz⟩ := p
    refine Prod.ext (Function.update_self _ _ _) (Subtype.ext ?_)
    change Function.update (Function.update z o y) o false = z
    rw [Function.update_idem, ← hz.2, Function.update_eq_self]
  right_inv z := Subtype.ext (by
    change Function.update (Function.update z.1 o false) o (z.1 o) = z.1
    rw [Function.update_idem, Function.update_eq_self])

/-- **The Bell test only succeeds as well as `B` is maximally mixed.** -/
theorem bellPr_le (b o : Fin W) (hbo : b ≠ o) (ξ : Qubits W × M → ℂ) :
    bellPr b o ξ ≤
      fidelity (margB b ξ) (diagonal fun _ : Bool => (((1 : ℝ) / 2 : ℝ) : ℂ)) ^ 2 := by
  set χ : Bool × (Bool × (Z00 b o × M)) → ℂ := fun p =>
    ξ (Function.update (Function.update p.2.2.1.1 o p.2.1) b p.1, p.2.2.2) with hχdef
  have h := bell_prob_le χ (1 : Matrix (Bool × (Z00 b o × M)) (Bool × (Z00 b o × M)) ℂ)
    (by rw [conjTranspose_one, Matrix.one_mul])
  rw [one_kronecker_one, one_mulVec, trace_bell_pureState] at h
  have hL : bellPr b o ξ = ∑ r : Z00 b o × M,
      ‖assocVec χ ((false, false), r) + assocVec χ ((true, true), r)‖ ^ 2 / 2 := by
    rw [bellPr, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun μ _ => ?_
    simp only [assocVec, χ]
    have h1 : Function.update z.1 o false = z.1 := Function.update_eq_self_iff.mpr z.2.2.symm
    have h2 : Function.update z.1 b false = z.1 := Function.update_eq_self_iff.mpr z.2.1.symm
    rw [h1, h2]
  have hR : traceRight (pureState χ) = margB b ξ := by
    ext x x'
    simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply, margB, of_apply]
    rw [← (splitO b o hbo).sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rfl
  rw [hL]
  rw [hR] at h
  exact h

/-- The one-wire embedding. -/
def wire1 (b : Fin W) : Fin 1 ↪ Fin W := ⟨fun _ => b, fun i j _ => Subsingleton.elim i j⟩

/-- `(Outside (wire1 b) → Bool) ≃ Z0 b`. -/
noncomputable def outsideZ0 (b : Fin W) : (Outside (wire1 b) → Bool) ≃ Z0 b where
  toFun z := ⟨(embSplit (wire1 b)).symm (fun _ => false, z), by
    have := congrArg (fun p => p.1 0) ((embSplit (wire1 b)).apply_symm_apply (fun _ => false, z))
    exact this⟩
  invFun z := (embSplit (wire1 b) z.1).2
  left_inv z := by
    change ((embSplit (wire1 b)) ((embSplit (wire1 b)).symm (fun _ => false, z))).2 = z
    rw [Equiv.apply_symm_apply]
  right_inv z := by
    apply Subtype.ext
    change (embSplit (wire1 b)).symm (fun _ => false, (embSplit (wire1 b) z.1).2) = z.1
    rw [Equiv.symm_apply_eq]
    refine Prod.ext (funext fun i => ?_) rfl
    exact z.2.symm

theorem embSplit_wire1_symm (b : Fin W) (a : Qubits 1) (z : Outside (wire1 b) → Bool) :
    (embSplit (wire1 b)).symm (a, z) = Function.update (outsideZ0 b z).1 b (a 0) := by
  have h := embSplit_symm_update (wire1 b) ((embSplit (wire1 b)).symm (fun _ => false, z)) 0 (a 0)
  rw [Equiv.apply_symm_apply] at h
  rw [show a = Function.update (fun _ => false) 0 (a 0) from
    funext fun i => by rw [Subsingleton.elim i 0, Function.update_self]]
  exact h

omit [DecidableEq M] in
/-- **`margB` is the reduced state on wire `b`.** -/
theorem margB_eq_reduceTo (b : Fin W) (ξ : Qubits W × M → ℂ) (a a' : Qubits 1) :
    margB b ξ (a 0) (a' 0) = reduceTo (wire1 b) (pureState ξ) a a' := by
  simp only [margB, reduceTo, of_apply, pureState, vecMulVec_apply, Pi.star_apply]
  rw [← (outsideZ0 b).sum_comp]
  simp only [embSplit_wire1_symm]

end ShiQIP
