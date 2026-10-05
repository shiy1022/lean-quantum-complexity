/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Choi

/-!
# Q07 — Kraus realization

Factor a PSD Choi matrix as `B * Bᴴ` and reshape each column `c` of `B` into the operator
`krausOfFactor B c : Matrix n m ℂ`, `(i, a) ↦ B (a, i) c`. Then:

* `ofChoi_mul_conjTranspose`: the map with Choi matrix `B * Bᴴ` is the Kraus map of these
  operators;
* `sum_krausOfFactor`: `∑ c, Kcᴴ * Kc` is the transpose of the output partial trace of `B * Bᴴ`,
  so a trace-preserving map gets exactly normalized Kraus operators.

Consequences, for arbitrary (possibly different) input and output registers:

* `isCP_iff_choi_posSemidef`: **CP ⇔ Choi PSD**;
* `IsCP.exists_kraus`: every CP map is a Kraus map with `card (m × n)` operators;
* `isChannel_iff_exists_kraus`: `Φ` is a channel iff it is a Kraus map with `∑ Kᴴ K = 1`.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {m n r : Type}

/-- Reshape column `c` of `B` into a Kraus operator `n ← m`. -/
def krausOfFactor (B : Matrix (m × n) r ℂ) (c : r) : Matrix n m ℂ :=
  Matrix.of fun i a => B (a, i) c

variable [Fintype m] [DecidableEq m] [Fintype n] [Fintype r]

omit [DecidableEq m] [Fintype n] in
/-- The map with Choi matrix `B * Bᴴ` is the Kraus map of the reshaped columns of `B`. -/
theorem ofChoi_mul_conjTranspose (B : Matrix (m × n) r ℂ) :
    ofChoi (B * Bᴴ) = krausMap (krausOfFactor B) := by
  apply LinearMap.ext
  intro X
  ext i j
  rw [krausMap_apply]
  simp only [ofChoi_apply, mul_apply, conjTranspose_apply, Matrix.sum_apply, krausOfFactor,
    of_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => by ring

omit [Fintype m] [DecidableEq m] in
/-- The Kraus normalization is the transposed output partial trace of the Choi matrix. -/
theorem sum_krausOfFactor (B : Matrix (m × n) r ℂ) :
    ∑ c, (krausOfFactor B c)ᴴ * krausOfFactor B c = (traceRight (B * Bᴴ))ᵀ := by
  ext a b
  simp only [mul_apply, conjTranspose_apply, Matrix.sum_apply, krausOfFactor, of_apply,
    traceRight_apply, transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by ring

section

variable [DecidableEq n]

/-- **CP ⇔ Choi PSD.** -/
theorem isCP_iff_choi_posSemidef (Φ : MatMap m n) : IsCP Φ ↔ (choi Φ).PosSemidef := by
  refine ⟨IsCP.choi_posSemidef, fun h => ?_⟩
  obtain ⟨B, hB⟩ := PSD_exists_eq_mul_conjTranspose h
  rw [← ofChoi_choi Φ, hB, ofChoi_mul_conjTranspose]
  exact isCP_krausMap _

/-- **Kraus representation**: every CP map is a Kraus map with `card (m × n)` operators. -/
theorem IsCP.exists_kraus {Φ : MatMap m n} (h : IsCP Φ) :
    ∃ K : m × n → Matrix n m ℂ, Φ = krausMap K := by
  obtain ⟨B, hB⟩ := PSD_exists_eq_mul_conjTranspose h.choi_posSemidef
  exact ⟨krausOfFactor B, by rw [← ofChoi_choi Φ, hB, ofChoi_mul_conjTranspose]⟩

/-- **Channels are exactly normalized Kraus maps.** -/
theorem isChannel_iff_exists_kraus (Φ : MatMap m n) :
    IsChannel Φ ↔ ∃ K : m × n → Matrix n m ℂ, Φ = krausMap K ∧ ∑ c, (K c)ᴴ * K c = 1 := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := PSD_exists_eq_mul_conjTranspose h.cp.choi_posSemidef
    refine ⟨krausOfFactor B, by rw [← ofChoi_choi Φ, hB, ofChoi_mul_conjTranspose], ?_⟩
    rw [sum_krausOfFactor, ← hB, (isTP_iff_traceRight_choi Φ).mp h.tp, transpose_one]
  · rintro ⟨K, rfl, hK⟩
    exact isChannel_krausMap hK

end

end ShiQuantum
