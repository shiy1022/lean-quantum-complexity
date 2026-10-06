/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.UhlmannGeneral
import Quantum.ChannelTensor

/-!
# Q19 (support) — completing a contraction to a channel, and pure-state algebra

* Pure-state algebra: `kronecker_pureState`, `reindex_pureState`, `liftR_conjMap_pureState`,
  `liftR_sum`.
* **Completion.** For `K : Matrix F E ℂ` with `Kᴴ K ≤ 1` and `F` nonempty, `completeKraus K f₀`
  adds Kraus operators `|f₀⟩⟨row e of √(1 - Kᴴ K)|`, which makes the operators sum to the identity
  (`isChannel_completeKraus`).
* **Vanishing.** If `(1 ⊗ K)` preserves the norm of a vector `v`, then every added operator kills
  `v` (`completeKraus_some_mulVec`), so on `|v⟩⟨v|` the completed channel acts as conjugation by
  `1 ⊗ K` alone (`liftR_completeKraus_pureState`).
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {α β H E F : Type}

/-! ## Pure-state algebra -/

theorem kronecker_pureState [Fintype α] [Fintype β] (u : α → ℂ) (v : β → ℂ) :
    pureState u ⊗ₖ pureState v = pureState (fun p : α × β => u p.1 * v p.2) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [pureState, vecMulVec_apply, star_mul']
  ring

theorem reindex_pureState (e : α ≃ β) (v : α → ℂ) :
    Matrix.reindex e e (pureState v) = pureState (v ∘ e.symm) := by
  ext a b; rfl

theorem liftR_conjMap_pureState [Fintype H] [DecidableEq H] [Fintype E] (K : Matrix F E ℂ)
    (v : H × E → ℂ) :
    liftR H (conjMap K) (pureState v) = pureState (((1 : Matrix H H ℂ) ⊗ₖ K) *ᵥ v) := by
  rw [liftR_conjMap, pureState, mul_vecMulVec, vecMulVec_mul, pureState, star_mulVec]

theorem liftR_sum {ι : Type*} [Fintype ι] {m n : Type} (Φ : ι → MatMap m n)
    (X : Matrix (H × m) (H × m) ℂ) : liftR H (∑ i, Φ i) X = ∑ i, liftR H (Φ i) X := by
  ext P Q
  simp [liftR_apply, LinearMap.sum_apply, Matrix.sum_apply]

/-! ## Completion of a contraction -/

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

/-- The Kraus operators completing `K`: `K` itself, and `|f₀⟩⟨row e of √(1 - Kᴴ K)|`. -/
noncomputable def completeKraus (K : Matrix F E ℂ) (f₀ : F) : Option E → Matrix F E ℂ
  | none => K
  | some e => vecMulVec (Pi.single f₀ 1) (psdSqrt (1 - Kᴴ * K) e)

omit [DecidableEq E] [Fintype F] [DecidableEq F] in
theorem sum_vecMulVec_rows (D : Matrix E E ℂ) :
    ∑ e, vecMulVec (star (D e)) (D e) = Dᴴ * D := by
  ext a b
  simp [vecMulVec_apply, mul_apply, conjTranspose_apply, Matrix.sum_apply]

theorem completeKraus_sum {K : Matrix F E ℂ} (hK : Kᴴ * K ≤ 1) (f₀ : F) :
    ∑ o, (completeKraus K f₀ o)ᴴ * completeKraus K f₀ o = 1 := by
  have hD : (1 - Kᴴ * K).PosSemidef := Matrix.le_iff.mp hK
  rw [Fintype.sum_option]
  simp only [completeKraus]
  have e1 : ∀ e, (vecMulVec (Pi.single f₀ (1 : ℂ)) (psdSqrt (1 - Kᴴ * K) e))ᴴ *
      vecMulVec (Pi.single f₀ 1) (psdSqrt (1 - Kᴴ * K) e) =
      vecMulVec (star (psdSqrt (1 - Kᴴ * K) e)) (psdSqrt (1 - Kᴴ * K) e) := by
    intro e
    rw [conjTranspose_vecMulVec, vecMulVec_mul_vecMulVec]
    simp [dotProduct_single]
  simp only [e1]
  rw [sum_vecMulVec_rows, psdSqrt_conjTranspose, psdSqrt_mul_self hD]
  abel

theorem isChannel_completeKraus {K : Matrix F E ℂ} (hK : Kᴴ * K ≤ 1) (f₀ : F) :
    IsChannel (krausMap (completeKraus K f₀)) :=
  isChannel_krausMap (completeKraus_sum hK f₀)

/-! ## Vanishing of the added operators -/

omit [DecidableEq E] [Fintype F] [DecidableEq F] in
theorem one_kronecker_mulVec_apply [Fintype H] [DecidableEq H] (A : Matrix F E ℂ)
    (v : H × E → ℂ) (h : H) (f : F) :
    (((1 : Matrix H H ℂ) ⊗ₖ A) *ᵥ v) (h, f) = ∑ e, A f e * v (h, e) := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply, one_apply, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single h]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem completeKraus_some_mulVec [Fintype H] [DecidableEq H] {K : Matrix F E ℂ} (hK : Kᴴ * K ≤ 1)
    (f₀ : F) {v : H × E → ℂ}
    (hv : star (((1 : Matrix H H ℂ) ⊗ₖ K) *ᵥ v) ⬝ᵥ (((1 : Matrix H H ℂ) ⊗ₖ K) *ᵥ v) =
      star v ⬝ᵥ v) (e : E) :
    ((1 : Matrix H H ℂ) ⊗ₖ completeKraus K f₀ (some e)) *ᵥ v = 0 := by
  set D := psdSqrt (1 - Kᴴ * K)
  have hD : (1 - Kᴴ * K).PosSemidef := Matrix.le_iff.mp hK
  -- the quadratic form of `1 ⊗ (1 - Kᴴ K)` vanishes at `v`
  have hG : star v ⬝ᵥ (((1 : Matrix H H ℂ) ⊗ₖ (1 - Kᴴ * K)) *ᵥ v) = 0 := by
    rw [kronecker_sub', one_kronecker_one, sub_mulVec, dotProduct_sub, one_mulVec]
    have : ((1 : Matrix H H ℂ) ⊗ₖ (Kᴴ * K)) = ((1 : Matrix H H ℂ) ⊗ₖ K)ᴴ * ((1 : Matrix H H ℂ) ⊗ₖ K) := by
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [this, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hv, sub_self]
  -- hence `(1 ⊗ D) v = 0`
  have hDD : (1 : Matrix H H ℂ) ⊗ₖ (1 - Kᴴ * K) = ((1 : Matrix H H ℂ) ⊗ₖ D)ᴴ * ((1 : Matrix H H ℂ) ⊗ₖ D) := by
    rw [conjTranspose_kronecker, conjTranspose_one, psdSqrt_conjTranspose, ← mul_kronecker_mul,
      Matrix.one_mul, psdSqrt_mul_self hD]
  have hzero : ((1 : Matrix H H ℂ) ⊗ₖ D) *ᵥ v = 0 := by
    rw [hDD, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec] at hG
    exact dotProduct_star_self_eq_zero.mp hG
  funext ⟨h, f⟩
  rw [one_kronecker_mulVec_apply]
  have := congrFun hzero (h, e)
  rw [one_kronecker_mulVec_apply] at this
  simp only [completeKraus, vecMulVec_apply, Pi.zero_apply]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [this]; simp

/-- On a norm-preserved pure state, the completed channel acts as conjugation by `1 ⊗ K`. -/
theorem liftR_completeKraus_pureState [Fintype H] [DecidableEq H] {K : Matrix F E ℂ}
    (hK : Kᴴ * K ≤ 1) (f₀ : F) {v : H × E → ℂ}
    (hv : star (((1 : Matrix H H ℂ) ⊗ₖ K) *ᵥ v) ⬝ᵥ (((1 : Matrix H H ℂ) ⊗ₖ K) *ᵥ v) =
      star v ⬝ᵥ v) :
    liftR H (krausMap (completeKraus K f₀)) (pureState v) =
      pureState (((1 : Matrix H H ℂ) ⊗ₖ K) *ᵥ v) := by
  rw [krausMap, liftR_sum, Fintype.sum_option]
  simp only [liftR_conjMap_pureState, completeKraus_some_mulVec hK f₀ hv]
  simp [completeKraus, pureState]

end ShiQuantum
