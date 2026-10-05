import Quantum.Measurement

/-! Fresh-import audit for Q04: exact statement types, then transitive axioms. -/

open ShiQuantum Matrix
open scoped ComplexOrder MatrixOrder

#check (IsDensity.mix : ∀ {n : Type} [Fintype n] {ρ σ : Matrix n n ℂ}, IsDensity ρ →
  IsDensity σ → ∀ {p : ℝ}, 0 ≤ p → p ≤ 1 → IsDensity (p • ρ + (1 - p) • σ))
#check (isDensity_pure_iff : ∀ {n : Type} [Fintype n] (v : n → ℂ),
  IsDensity (pureState v) ↔ ∑ i, ‖v i‖ ^ 2 = 1)
#check (isDensity_unique_iff : ∀ {n : Type} [Fintype n] [Unique n] [DecidableEq n]
  (ρ : Matrix n n ℂ), IsDensity ρ ↔ ρ = 1)
#check (prob_mem_Icc : ∀ {n : Type} [Fintype n] [DecidableEq n] {E ρ : Matrix n n ℂ},
  IsEffect E → IsDensity ρ → prob E ρ ∈ Set.Icc 0 1)
#check (prob_compl : ∀ {n : Type} [Fintype n] [DecidableEq n] {E ρ : Matrix n n ℂ},
  IsDensity ρ → prob (1 - E) ρ = 1 - prob E ρ)
#check (prob_basisEffect_pureState : ∀ {n : Type} [Fintype n] [DecidableEq n] (p : n → Prop)
  [DecidablePred p] (v : n → ℂ),
  prob (basisEffect p) (pureState v) = ∑ i, if p i then ‖v i‖ ^ 2 else 0)
#check (prob : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ → ℝ)
example {n : Type} [Fintype n] [DecidableEq n] (E ρ : Matrix n n ℂ) :
    prob E ρ = (trace (E * ρ)).re := rfl

#print axioms ShiQuantum.IsDensity.isHermitian
#print axioms ShiQuantum.IsDensity.re_trace
#print axioms ShiQuantum.IsDensity.mix
#print axioms ShiQuantum.pureState_posSemidef
#print axioms ShiQuantum.trace_pureState
#print axioms ShiQuantum.isDensity_pure_iff
#print axioms ShiQuantum.isDensity_pure_iff_norm
#print axioms ShiQuantum.isDensity_maxMixed
#print axioms ShiQuantum.maxMixed_unique
#print axioms ShiQuantum.maxMixed_unique_eq_pure
#print axioms ShiQuantum.isDensity_unique_iff
#print axioms ShiQuantum.IsEffect.posSemidef
#print axioms ShiQuantum.IsEffect.compl
#print axioms ShiQuantum.isEffect_zero
#print axioms ShiQuantum.isEffect_one
#print axioms ShiQuantum.prob_nonneg
#print axioms ShiQuantum.prob_one
#print axioms ShiQuantum.prob_sub
#print axioms ShiQuantum.prob_add
#print axioms ShiQuantum.prob_compl
#print axioms ShiQuantum.prob_le_one
#print axioms ShiQuantum.prob_mem_Icc
#print axioms ShiQuantum.prob_mix
#print axioms ShiQuantum.prob_mono
#print axioms ShiQuantum.prob_pureState
#print axioms ShiQuantum.isEffect_basisEffect
#print axioms ShiQuantum.prob_basisEffect_pureState
#print axioms ShiQuantum.prob_basisEffect_true_pureState
#print axioms ShiQuantum.plusVec_sq
