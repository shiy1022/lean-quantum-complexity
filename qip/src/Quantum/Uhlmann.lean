/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Fidelity

/-!
# Q11 — Uhlmann's theorem (common environment `n`)

For density operators `ρ, σ` on `n` and purifications on the environment `n`:

* `uhlmann_le`: every pair of purifications `ψ` of `ρ` and `φ` of `σ` has
  `‖⟨ψ, φ⟩‖ ≤ fidelity ρ σ`;
* `uhlmann_attained`: the canonical purification `purify ρ` and an explicitly constructed
  purification `φ` of `σ` (`√σ V`, with `V` the unitary maximizing `‖tr (V √ρ √σ)‖`) satisfy
  `⟨purify ρ, φ⟩ = fidelity ρ σ`. The maximum is attained by a witness; it is not only a
  supremum.

The overlap of vectorized matrices is a trace: `⟨vec M, vec N⟩ = tr (Mᴴ N)`
(`star_matToVec_dotProduct`). Zero singular values are allowed throughout (the polar unitary
of `Quantum.Polar` has no rank hypothesis).

**Scope of this file.** The environment is fixed to the system register `n`. Environments of
other sizes, and the monotonicity of fidelity under partial trace, are not yet proved here
(see the progress ledger).
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n E : Type} [Fintype n] [DecidableEq n] [Fintype E]

omit [DecidableEq n] in
/-- The overlap of two vectorized matrices is `tr (Mᴴ N)`. -/
theorem star_matToVec_dotProduct (M N : Matrix n E ℂ) :
    star (matToVec M) ⬝ᵥ matToVec N = trace (Mᴴ * N) := by
  simp only [dotProduct, matToVec, Pi.star_apply, trace, diag_apply, mul_apply,
    conjTranspose_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- **Uhlmann, upper bound.** -/
theorem uhlmann_le {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {ψ φ : n × n → ℂ} (hψ : IsPurification ψ ρ) (hφ : IsPurification φ σ) :
    ‖star ψ ⬝ᵥ φ‖ ≤ fidelity ρ σ := by
  rw [isPurification_iff] at hψ hφ
  have h1 : psdSqrt ρ * (psdSqrt ρ)ᴴ = vecToMat ψ * (vecToMat ψ)ᴴ := by
    rw [psdSqrt_mul_conjTranspose hρ, hψ]
  have h2 : psdSqrt σ * (psdSqrt σ)ᴴ = vecToMat φ * (vecToMat φ)ᴴ := by
    rw [psdSqrt_mul_conjTranspose hσ, hφ]
  obtain ⟨U, hU, hMU⟩ := exists_unitary_of_mul_conjTranspose_eq h1
  obtain ⟨V, hV, hNV⟩ := exists_unitary_of_mul_conjTranspose_eq h2
  have hψ' : ψ = matToVec (vecToMat ψ) := rfl
  have hφ' : φ = matToVec (vecToMat φ) := rfl
  rw [hψ', hφ', star_matToVec_dotProduct, hMU, hNV, conjTranspose_mul, psdSqrt_conjTranspose]
  -- tr (Uᴴ √ρ √σ V) = tr ((V Uᴴ) (√ρ √σ))
  have e : trace (Uᴴ * psdSqrt ρ * (psdSqrt σ * V)) =
      trace (V * Uᴴ * (psdSqrt ρ * psdSqrt σ)) := by
    rw [show Uᴴ * psdSqrt ρ * (psdSqrt σ * V) = Uᴴ * (psdSqrt ρ * psdSqrt σ) * V by
      simp only [Matrix.mul_assoc]]
    rw [trace_mul_cycle, Matrix.mul_assoc]
  rw [e]
  have hW : V * Uᴴ ∈ Matrix.unitaryGroup n ℂ :=
    Submonoid.mul_mem _ hV (conjTranspose_mem_unitaryGroup hU)
  calc ‖trace (V * Uᴴ * (psdSqrt ρ * psdSqrt σ))‖
      ≤ (trace (absM (psdSqrt ρ * psdSqrt σ))).re := norm_trace_mul_le hW
    _ = fidelity σ ρ := (fidelity_eq_traceNorm hρ).symm
    _ = fidelity ρ σ := fidelity_symm hσ hρ

/-- **Uhlmann, attained**: an explicit pair of purifications realizes the root fidelity. -/
theorem uhlmann_attained {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∃ φ : n × n → ℂ, IsPurification φ σ ∧
      star (purify ρ) ⬝ᵥ φ = (fidelity ρ σ : ℂ) := by
  obtain ⟨V, hV, hVA⟩ := exists_unitary_trace_eq_absM (psdSqrt ρ * psdSqrt σ)
  refine ⟨matToVec (psdSqrt σ * V), ?_, ?_⟩
  · rw [isPurification_iff, vecToMat_matToVec, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc V, unitary_mul_conjTranspose hV, Matrix.one_mul,
      psdSqrt_mul_conjTranspose hσ]
  · rw [purify, star_matToVec_dotProduct, psdSqrt_conjTranspose, ← Matrix.mul_assoc,
      trace_mul_comm, hVA, fidelity_symm hρ hσ,
      fidelity_eq_traceNorm hρ, trace_absM_real]

/-- Root fidelity as a maximum over purifications on the environment `n`. -/
theorem fidelity_eq_max_overlap {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (∀ ψ φ : n × n → ℂ, IsPurification ψ ρ → IsPurification φ σ →
        ‖star ψ ⬝ᵥ φ‖ ≤ fidelity ρ σ) ∧
      ∃ ψ φ : n × n → ℂ, IsPurification ψ ρ ∧ IsPurification φ σ ∧
        ‖star ψ ⬝ᵥ φ‖ = fidelity ρ σ := by
  refine ⟨fun ψ φ hψ hφ => uhlmann_le hρ hσ hψ hφ, ?_⟩
  obtain ⟨φ, hφ, hov⟩ := uhlmann_attained hρ hσ
  refine ⟨purify ρ, φ, purify_isPurification hρ, hφ, ?_⟩
  rw [hov, Complex.norm_real, Real.norm_of_nonneg (fidelity_nonneg ρ σ)]

end ShiQuantum
