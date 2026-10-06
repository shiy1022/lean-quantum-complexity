/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.UhlmannGeneral

/-!
# Q30 — Uhlmann's theorem, attained on an arbitrary environment

For purifications `ψ`, `φ` of `ρ`, `σ` on any environment `E`, a unitary on `E × n` (an ancilla
of the system's size, started in a fixed basis state) aligns them up to the root fidelity
(**`exists_unitary_overlap_eq_fidelity`**).
-/


namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {n E : Type} [Fintype n] [DecidableEq n] [Fintype E] [DecidableEq E]

/-- Add the ancilla `n` in the basis state `a₀`. -/
def addAnc (a₀ : n) (ψ : n × E → ℂ) : n × (E × n) → ℂ :=
  fun p => if p.2.2 = a₀ then ψ (p.1, p.2.1) else 0

/-- Put a purification on the environment `n` into `E × n`, at `e₀`. -/
def putEnv (e₀ : E) (p : n × n → ℂ) : n × (E × n) → ℂ :=
  fun q => if q.2.1 = e₀ then p (q.1, q.2.2) else 0

theorem isPurification_addAnc (a₀ : n) {ψ : n × E → ℂ} {ρ : Matrix n n ℂ}
    (h : IsPurification ψ ρ) : IsPurification (addAnc a₀ ψ) ρ := by
  unfold IsPurification at h ⊢
  rw [← h]
  ext i j
  simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply, addAnc,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha; simp [ha]
  · simp

theorem isPurification_putEnv (e₀ : E) {p : n × n → ℂ} {ρ : Matrix n n ℂ}
    (h : IsPurification p ρ) : IsPurification (putEnv e₀ p) ρ := by
  unfold IsPurification at h ⊢
  rw [← h]
  ext i j
  simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply, putEnv,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro e _ he; simp [he]
  · simp

theorem dot_putEnv (e₀ : E) (p q : n × n → ℂ) :
    star (putEnv e₀ q) ⬝ᵥ putEnv e₀ p = star q ⬝ᵥ p := by
  simp only [dotProduct, putEnv, Pi.star_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro e _ he; simp [he]
  · simp

/-- **Uhlmann, attained on an arbitrary environment** (with an ancilla). -/
theorem exists_unitary_overlap_eq_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) {ψ φ : n × E → ℂ} (hψ : IsPurification ψ ρ) (hφ : IsPurification φ σ)
    (e₀ : E) (a₀ : n) :
    ∃ W ∈ Matrix.unitaryGroup (E × n) ℂ,
      star (addAnc a₀ φ) ⬝ᵥ (((1 : Matrix n n ℂ) ⊗ₖ W) *ᵥ addAnc a₀ ψ) = (fidelity ρ σ : ℂ) := by
  obtain ⟨q, hq, hpq⟩ := uhlmann_attained hρ hσ
  obtain ⟨U₁, hU₁, h₁⟩ := (isPurification_addAnc a₀ hψ).exists_unitary
    (isPurification_putEnv e₀ (purify_isPurification hρ))
  obtain ⟨U₂, hU₂, h₂⟩ := (isPurification_addAnc a₀ hφ).exists_unitary
    (isPurification_putEnv e₀ hq)
  have hU₁' := Matrix.mem_unitaryGroup_iff.mp hU₁
  have hU₂' := Matrix.mem_unitaryGroup_iff.mp hU₂
  have hM : (U₁ * U₂ᴴ) * (U₁ * U₂ᴴ)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U₂ᴴ, show U₂ᴴ * U₂ = 1 from Matrix.mem_unitaryGroup_iff'.mp hU₂,
      Matrix.one_mul]
    exact hU₁'
  refine ⟨(U₁ * U₂ᴴ)ᵀ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    change ((U₁ * U₂ᴴ)ᵀ)ᴴ * (U₁ * U₂ᴴ)ᵀ = 1
    have e : ((U₁ * U₂ᴴ)ᵀ)ᴴ = ((U₁ * U₂ᴴ)ᴴ)ᵀ := by
      ext a b; simp only [conjTranspose_apply, transpose_apply]
    rw [e, ← transpose_mul, hM, transpose_one]
  · rw [← matToVec_mul, show addAnc a₀ φ = matToVec (vecToMat (addAnc a₀ φ)) from rfl,
      star_matToVec_dotProduct]
    have e1 : (vecToMat (addAnc a₀ φ))ᴴ * (vecToMat (addAnc a₀ ψ) * (U₁ * U₂ᴴ)) =
        (vecToMat (addAnc a₀ φ))ᴴ * vecToMat (addAnc a₀ ψ) * U₁ * U₂ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e1, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    have e2 : U₂ᴴ * (vecToMat (addAnc a₀ φ))ᴴ * vecToMat (addAnc a₀ ψ) * U₁ =
        (vecToMat (putEnv e₀ q))ᴴ * vecToMat (putEnv e₀ (purify ρ)) := by
      rw [h₁, h₂, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e2, ← star_matToVec_dotProduct]
    change star (putEnv e₀ q) ⬝ᵥ putEnv e₀ (purify ρ) = _
    rw [dot_putEnv]
    have h := congrArg star hpq
    rw [Matrix.star_dotProduct, star_star] at h
    rw [h]
    simp

end ShiQuantum
