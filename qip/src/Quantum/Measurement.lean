/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.State

/-!
# Q04 — effects and measurement probabilities

An effect is a matrix `E` with `0 ≤ E ≤ 1` in the Loewner order (`IsEffect`). The probability of
the outcome `E` on `ρ` is `prob E ρ = Re (trace (E * ρ))`. Proved here, not assumed:

* `prob_mem_Icc`: the probability lies in `[0, 1]`;
* `prob_compl`: the complementary effect `1 - E` has probability `1 - prob E ρ`;
* `prob_mix`: probabilities are affine in the state;
* `prob_mono`: probabilities are monotone in the effect;
* `prob_pureState`: on a pure state, `prob E |v⟩⟨v| = Re ⟨v, E v⟩`;
* `prob_basisEffect_pureState`: for the basis projector onto `{i | p i}`, the probability on a pure
  state is the direct sum of squared amplitudes `∑ i, if p i then ‖v i‖ ^ 2 else 0`. This is the
  form of `ShiShallow.acceptProb`; the circuit-level identification is Q16.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An effect: `0 ≤ E ≤ 1` in the Loewner order. -/
structure IsEffect (E : Matrix n n ℂ) : Prop where
  nonneg : 0 ≤ E
  le_one : E ≤ 1

omit [Fintype n] in
theorem IsEffect.posSemidef {E : Matrix n n ℂ} (h : IsEffect E) : E.PosSemidef :=
  h.nonneg.posSemidef

omit [Fintype n] in
theorem IsEffect.compl {E : Matrix n n ℂ} (h : IsEffect E) : IsEffect (1 - E) :=
  ⟨sub_nonneg.mpr h.le_one, sub_le_self _ h.nonneg⟩

omit [Fintype n] in
theorem isEffect_zero : IsEffect (0 : Matrix n n ℂ) := ⟨le_rfl, PosSemidef.one.nonneg⟩

omit [Fintype n] in
theorem isEffect_one : IsEffect (1 : Matrix n n ℂ) := ⟨PosSemidef.one.nonneg, le_rfl⟩

/-- The probability of outcome `E` on state `ρ`. -/
noncomputable def prob (E ρ : Matrix n n ℂ) : ℝ := (trace (E * ρ)).re

omit [DecidableEq n] in
theorem prob_nonneg {E ρ : Matrix n n ℂ} (hE : E.PosSemidef) (hρ : IsDensity ρ) :
    0 ≤ prob E ρ := by
  classical
  exact psd_re_trace_mul_nonneg hE hρ.posSemidef

theorem prob_one {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) : prob 1 ρ = 1 := by
  rw [prob, Matrix.one_mul, hρ.re_trace]

omit [DecidableEq n] in
theorem prob_sub (E F ρ : Matrix n n ℂ) : prob (E - F) ρ = prob E ρ - prob F ρ := by
  rw [prob, prob, prob, Matrix.sub_mul, trace_sub, Complex.sub_re]

omit [DecidableEq n] in
theorem prob_add (E F ρ : Matrix n n ℂ) : prob (E + F) ρ = prob E ρ + prob F ρ := by
  rw [prob, prob, prob, Matrix.add_mul, trace_add, Complex.add_re]

/-- Complementary outcomes have probabilities summing to one. -/
theorem prob_compl {E ρ : Matrix n n ℂ} (hρ : IsDensity ρ) : prob (1 - E) ρ = 1 - prob E ρ := by
  rw [prob_sub, prob_one hρ]

theorem prob_le_one {E ρ : Matrix n n ℂ} (hE : IsEffect E) (hρ : IsDensity ρ) : prob E ρ ≤ 1 := by
  have := prob_nonneg hE.compl.posSemidef hρ
  rw [prob_compl hρ] at this
  linarith

theorem prob_mem_Icc {E ρ : Matrix n n ℂ} (hE : IsEffect E) (hρ : IsDensity ρ) :
    prob E ρ ∈ Set.Icc 0 1 :=
  ⟨prob_nonneg hE.posSemidef hρ, prob_le_one hE hρ⟩

omit [DecidableEq n] in
/-- Probabilities are affine in the state. -/
theorem prob_mix (E ρ σ : Matrix n n ℂ) (p : ℝ) :
    prob E (p • ρ + (1 - p) • σ) = p * prob E ρ + (1 - p) * prob E σ := by
  simp only [prob, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, Complex.add_re,
    Complex.real_smul, Complex.re_ofReal_mul]

omit [DecidableEq n] in
/-- Probabilities are monotone in the effect. -/
theorem prob_mono {E F ρ : Matrix n n ℂ} (hEF : E ≤ F) (hρ : IsDensity ρ) :
    prob E ρ ≤ prob F ρ := by
  classical
  exact (Complex.le_def.mp (trace_mul_mono hEF hρ.posSemidef)).1

omit [DecidableEq n] in
/-- On a pure state the probability is the quadratic form `Re ⟨v, E v⟩`. -/
theorem prob_pureState (E : Matrix n n ℂ) (v : n → ℂ) :
    prob E (pureState v) = (star v ⬝ᵥ (E *ᵥ v)).re := by
  rw [prob, pureState, trace_mul_rankOne]

/-! ## Basis projectors -/

/-- The projector onto the basis states satisfying `p`. -/
def basisEffect (p : n → Prop) [DecidablePred p] : Matrix n n ℂ :=
  diagonal fun i => if p i then 1 else 0

omit [Fintype n] in
theorem isEffect_basisEffect (p : n → Prop) [DecidablePred p] : IsEffect (basisEffect p) := by
  constructor
  · refine (PosSemidef.diagonal fun i => ?_).nonneg
    simp only [Pi.zero_apply]
    split_ifs <;> simp
  · rw [Matrix.le_iff, basisEffect, ← diagonal_one, diagonal_sub]
    refine PosSemidef.diagonal fun i => ?_
    simp only [Pi.zero_apply]
    split_ifs <;> simp

/-- **Pure-state measurement is a sum of squared amplitudes.** -/
theorem prob_basisEffect_pureState (p : n → Prop) [DecidablePred p] (v : n → ℂ) :
    prob (basisEffect p) (pureState v) = ∑ i, if p i then ‖v i‖ ^ 2 else 0 := by
  rw [prob_pureState]
  simp only [basisEffect, mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [one_mul, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  · simp

/-- The total probability of all basis outcomes of a normalized pure state is one. -/
theorem prob_basisEffect_true_pureState (v : n → ℂ) :
    prob (basisEffect fun _ => True) (pureState v) = ∑ i, ‖v i‖ ^ 2 := by
  simp [prob_basisEffect_pureState]

/-! ## Examples -/

/-- The amplitudes of `|+⟩ = (|0⟩ + |1⟩) / √2`. -/
noncomputable def plusVec : Bool → ℂ := fun _ => ((Real.sqrt 2)⁻¹ : ℝ)

theorem plusVec_sq (b : Bool) : ‖plusVec b‖ ^ 2 = 1 / 2 := by
  rw [plusVec, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

example : IsDensity (pureState plusVec) := by
  rw [isDensity_pure_iff, Fintype.sum_bool, plusVec_sq, plusVec_sq]; norm_num

/-- Measuring `|+⟩` in the computational basis gives outcome `1` with probability `1/2`. -/
example : prob (basisEffect fun b : Bool => b = true) (pureState plusVec) = 1 / 2 := by
  rw [prob_basisEffect_pureState, Fintype.sum_bool]
  simp [plusVec_sq]

/-- A zero-qubit register carries exactly one state, the maximally mixed one. -/
example : IsDensity (maxMixed (Qubits 0)) := isDensity_maxMixed

end ShiQuantum
