/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.HilbertBridge

/-!
# Q04 — density operators

A density operator on a finite register `n` is a PSD complex matrix with trace one
(`IsDensity`). Both conditions are hypotheses of the predicate; nothing is assumed about a
density operator beyond them. `Density n` is the corresponding subtype.

* Convex mixtures `p • ρ + (1 - p) • σ` (real `p ∈ [0, 1]`) are density operators.
* The pure state of a vector `v` is the rank-one matrix `|v⟩⟨v| = vecMulVec v (star v)`; it is a
  density operator **iff** `∑ i, ‖v i‖ ^ 2 = 1` (`isDensity_pure_iff`), i.e. iff `v` is a unit
  vector in the Hilbert norm (`isDensity_pure_iff_norm`).
* The maximally mixed state `(card n)⁻¹ • 1` is a density operator for every nonempty `n`. On a
  one-dimensional register (for instance zero qubits) it is the matrix `1`, which is also the pure
  state of the vector `1`.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n]

/-- A density operator: positive semidefinite with trace one. -/
structure IsDensity (ρ : Matrix n n ℂ) : Prop where
  posSemidef : ρ.PosSemidef
  trace_eq_one : trace ρ = 1

/-- The density operators on register `n`. -/
def Density (n : Type*) [Fintype n] := {ρ : Matrix n n ℂ // IsDensity ρ}

theorem IsDensity.isHermitian {ρ : Matrix n n ℂ} (h : IsDensity ρ) : ρ.IsHermitian :=
  h.posSemidef.isHermitian

theorem IsDensity.re_trace {ρ : Matrix n n ℂ} (h : IsDensity ρ) : (trace ρ).re = 1 := by
  rw [h.trace_eq_one, Complex.one_re]

/-- Real convex combinations of density operators are density operators. -/
theorem IsDensity.mix {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsDensity (p • ρ + (1 - p) • σ) where
  posSemidef := (hρ.posSemidef.smul hp0).add (hσ.posSemidef.smul (by linarith))
  trace_eq_one := by
    rw [trace_add, trace_smul, trace_smul, hρ.trace_eq_one, hσ.trace_eq_one]
    simp only [Complex.real_smul, mul_one]
    push_cast
    ring

/-! ## Pure states -/

/-- The pure state `|v⟩⟨v|`. -/
def pureState (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

theorem pureState_posSemidef (v : n → ℂ) : (pureState v).PosSemidef := rankOne_posSemidef v

theorem trace_pureState (v : n → ℂ) :
    trace (pureState v) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  rw [pureState, trace_rankOne, star_dotProduct_self']

/-- A pure state is normalized exactly when the squared amplitudes sum to one. -/
theorem isDensity_pure_iff (v : n → ℂ) : IsDensity (pureState v) ↔ ∑ i, ‖v i‖ ^ 2 = 1 := by
  constructor
  · intro h
    have := h.trace_eq_one
    rw [trace_pureState] at this
    exact_mod_cast this
  · intro h
    exact ⟨pureState_posSemidef v, by rw [trace_pureState, h]; simp⟩

theorem isDensity_pure_iff_norm (v : n → ℂ) : IsDensity (pureState v) ↔ ‖toE v‖ = 1 := by
  rw [isDensity_pure_iff, ← norm_toE_sq]
  constructor
  · intro h
    have h0 := norm_nonneg (toE v)
    nlinarith [sq_nonneg (‖toE v‖ - 1), sq_nonneg (‖toE v‖ + 1)]
  · intro h; rw [h]; norm_num

/-! ## The maximally mixed state -/

/-- The maximally mixed state `(card n)⁻¹ • 1`. -/
noncomputable def maxMixed (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  ((Fintype.card n : ℝ)⁻¹) • (1 : Matrix n n ℂ)

theorem isDensity_maxMixed [DecidableEq n] [Nonempty n] : IsDensity (maxMixed n) where
  posSemidef := PosSemidef.one.smul (by positivity)
  trace_eq_one := by
    have hc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [maxMixed, trace_smul, trace_one, Complex.real_smul]
    push_cast
    exact inv_mul_cancel₀ hc

/-- On a one-dimensional register the maximally mixed state is `1`. -/
theorem maxMixed_unique [Unique n] [DecidableEq n] : maxMixed n = 1 := by
  simp [maxMixed, Fintype.card_unique]

/-- On a one-dimensional register the maximally mixed state is pure: it is `|1⟩⟨1|`. -/
theorem maxMixed_unique_eq_pure [Unique n] [DecidableEq n] :
    maxMixed n = pureState (fun _ => 1) := by
  rw [maxMixed_unique]
  ext i j
  simp [pureState, vecMulVec_apply, Matrix.one_apply, Subsingleton.elim i j]

/-- The only density operator on a one-dimensional register is `1`. -/
theorem isDensity_unique_iff [Unique n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    IsDensity ρ ↔ ρ = 1 := by
  constructor
  · intro h
    have ht := h.trace_eq_one
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simpa [trace, Matrix.one_apply] using ht
  · rintro rfl
    rw [← maxMixed_unique]
    exact isDensity_maxMixed

end ShiQuantum
