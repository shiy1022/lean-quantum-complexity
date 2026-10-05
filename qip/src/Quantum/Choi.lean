/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.ChannelTensor

/-!
# Q07 — the Choi representation

**Convention (frozen).** For `Φ : MatMap m n` the Choi matrix lives on `m × n`, input register on
the left and output register on the right:

  `choi Φ (a, i) (b, j) = Φ (E a b) i j`,   `E a b = Matrix.single a b 1`.

It is **not** normalized: it is `id_m ⊗ Φ` applied to `|Ω⟩⟨Ω|`, where
`Ω = ∑ a, |a⟩ ⊗ |a⟩` is the unnormalized maximally entangled vector (`choi_eq_liftR`), so its
trace is `trace (Φ 1)`, which is `card m` for a channel.

* `ofChoi J` is the map `X ↦ (i, j) ↦ ∑ a b, X a b * J (a, i) (b, j)`. The two constructions are
  mutually inverse (`ofChoi_choi`, `choi_ofChoi`), for arbitrary input and output dimensions.
* `IsCP.choi_posSemidef`: a CP map has a PSD Choi matrix (the converse is in `Quantum.Kraus`).
* `isTP_iff_traceRight_choi`: `Φ` is trace preserving iff tracing the output out of its Choi
  matrix gives the identity on the input.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {m n : Type}

/-- The (unnormalized) Choi matrix, input factor first. -/
def choi [DecidableEq m] (Φ : MatMap m n) : Matrix (m × n) (m × n) ℂ :=
  Matrix.of fun P Q => Φ (Matrix.single P.1 Q.1 1) P.2 Q.2

@[simp] theorem choi_apply [DecidableEq m] (Φ : MatMap m n) (a b : m) (i j : n) :
    choi Φ (a, i) (b, j) = Φ (Matrix.single a b 1) i j := rfl

/-- The map with Choi matrix `J`. -/
def ofChoi [Fintype m] (J : Matrix (m × n) (m × n) ℂ) : MatMap m n where
  toFun X := Matrix.of fun i j => ∑ a, ∑ b, X a b * J (a, i) (b, j)
  map_add' X Y := by
    ext i j; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j; simp [Finset.mul_sum, mul_assoc]

@[simp] theorem ofChoi_apply [Fintype m] (J : Matrix (m × n) (m × n) ℂ) (X : Matrix m m ℂ)
    (i j : n) : ofChoi J X i j = ∑ a, ∑ b, X a b * J (a, i) (b, j) := rfl

/-- The unnormalized maximally entangled vector `∑ a, |a⟩|a⟩`. -/
def omegaVec (m : Type) [DecidableEq m] : m × m → ℂ := fun P => if P.1 = P.2 then 1 else 0

variable [Fintype m] [DecidableEq m]

/-- Every linear map is determined by its values on matrix units. -/
theorem map_eq_sum_single (Φ : MatMap m n) (X : Matrix m m ℂ) :
    Φ X = ∑ a, ∑ b, X a b • Φ (Matrix.single a b 1) := by
  conv_lhs => rw [matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_smul, smul_single, smul_eq_mul, mul_one]

/-- **Inverse identity**: a map is recovered from its Choi matrix. -/
theorem ofChoi_choi (Φ : MatMap m n) : ofChoi (choi Φ) = Φ := by
  apply LinearMap.ext
  intro X
  ext i j
  rw [map_eq_sum_single Φ X]
  simp [Matrix.sum_apply]

/-- **Inverse identity**: every matrix on `m × n` is the Choi matrix of exactly one map. -/
theorem choi_ofChoi (J : Matrix (m × n) (m × n) ℂ) : choi (ofChoi J) = J := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [choi_apply, ofChoi_apply, single_apply, ite_and, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx; simp [Ne.symm hx]
  · simp

theorem choi_injective : Function.Injective (choi : MatMap m n → _) := by
  intro Φ Ψ h
  rw [← ofChoi_choi Φ, h, ofChoi_choi]

omit [Fintype m] in
/-- The Choi matrix is `id ⊗ Φ` applied to `|Ω⟩⟨Ω|`. -/
theorem choi_eq_liftR (Φ : MatMap m n) :
    choi Φ = liftR m Φ (vecMulVec (omegaVec m) (star (omegaVec m))) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [choi_apply, liftR_apply]
  have : blockOf (vecMulVec (omegaVec m) (star (omegaVec m))) a b = Matrix.single a b 1 := by
    ext c d
    simp only [blockOf_apply, vecMulVec_apply, omegaVec, Pi.star_apply, single_apply]
    by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]
  rw [this]

omit [Fintype m] in
/-- The Choi matrix of the identity channel is `|Ω⟩⟨Ω|`. -/
theorem choi_id : choi (LinearMap.id : MatMap m m) = vecMulVec (omegaVec m) (star (omegaVec m)) := by
  rw [choi_eq_liftR, liftR_id, LinearMap.id_apply]

/-- **CP ⇒ Choi PSD.** -/
theorem IsCP.choi_posSemidef [Fintype n] {Φ : MatMap m n} (h : IsCP Φ) :
    (choi Φ).PosSemidef := by
  rw [choi_eq_liftR]
  exact h m _ (posSemidef_vecMulVec_self_star _)

/-! ## Trace preservation -/

omit [Fintype m] in
theorem traceRight_choi [Fintype n] (Φ : MatMap m n) (a b : m) :
    traceRight (choi Φ) a b = trace (Φ (Matrix.single a b 1)) := by
  simp [trace]

omit [DecidableEq m] in
theorem trace_ofChoi [Fintype n] (J : Matrix (m × n) (m × n) ℂ) (X : Matrix m m ℂ) :
    trace (ofChoi J X) = ∑ a, ∑ b, X a b * traceRight J a b := by
  simp only [trace, diag_apply, ofChoi_apply, traceRight_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- **TP ⇔ the output partial trace of the Choi matrix is the identity.** -/
theorem isTP_iff_traceRight_choi [Fintype n] (Φ : MatMap m n) :
    IsTP Φ ↔ traceRight (choi Φ) = 1 := by
  constructor
  · intro h
    ext a b
    rw [traceRight_choi, h]
    by_cases hab : a = b
    · subst hab; simp [trace]
    · rw [one_apply_ne hab]
      exact Finset.sum_eq_zero fun i _ => if_neg fun hi => hab (hi.1.trans hi.2.symm)
  · intro h X
    rw [← ofChoi_choi Φ, trace_ofChoi, h]
    simp [one_apply, trace]

end ShiQuantum
