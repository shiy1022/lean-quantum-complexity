/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Kraus

/-!
# Q08 — finite-dimensional dilation

**Stinespring.** Stack Kraus operators `K : ι → Matrix n m ℂ` into
`stinespring K : Matrix (n × ι) m ℂ`, `(i, c), a ↦ K c i a`. The environment register is `ι`.

* `stinespring_isometry`: `∑ Kᴴ K = 1` makes it an isometry, `Vᴴ V = 1`;
* `traceRight_stinespring`: discarding the environment gives back the Kraus map;
* `IsChannel.exists_stinespring`: every channel `Φ : MatMap m n` is `X ↦ Tr_E (V X Vᴴ)` for an
  isometry `V` with environment exactly `E = m × n`, so `card E = card m * card n`;
* `IsChannel.stinespring_ampliation`: the realization also holds **with an entangled
  reference system** `R`, i.e. for `id_R ⊗ Φ` on arbitrary inputs on `R × m`.

**Unitary extension.** `halmos V = [[V, 1 - V Vᴴ], [0, -Vᴴ]]` (rows `a ⊕ b`, columns `b ⊕ a`).
For an isometry it is unitary (`halmos_unitary`), and on the embedded input it acts as `V`
(`halmos_inl`). `halmosSq V` reorders its columns to a square unitary on `a ⊕ b`
(`halmosSq_mem_unitaryGroup`). The padding is a direct sum. Qubit-level (tensor) padding of
verifier circuits is Q17's concern; no efficiency claim is made for these dilations.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {m n ι R : Type}

/-! ## Stinespring isometries -/

/-- Stack Kraus operators into one operator into `output × environment`. -/
def stinespring (K : ι → Matrix n m ℂ) : Matrix (n × ι) m ℂ := Matrix.of fun P a => K P.2 P.1 a

/-- The partial trace over the environment, as a linear map. -/
def ptraceMap (n ι : Type) [Fintype ι] : MatMap (n × ι) n where
  toFun := traceRight
  map_add' := traceRight_add
  map_smul' := traceRight_smul

variable [Fintype m] [Fintype n] [Fintype ι]

omit [Fintype m] in
theorem stinespring_isometry {K : ι → Matrix n m ℂ} [DecidableEq m]
    (hK : ∑ c, (K c)ᴴ * K c = 1) : (stinespring K)ᴴ * stinespring K = 1 := by
  rw [← hK]
  ext a b
  simp only [mul_apply, conjTranspose_apply, stinespring, of_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]
  exact Finset.sum_comm

omit [Fintype m] [Fintype n] in
/-- Discarding the environment of the Stinespring isometry recovers the Kraus map. -/
theorem traceRight_stinespring [Fintype m] (K : ι → Matrix n m ℂ) (X : Matrix m m ℂ) :
    traceRight (stinespring K * X * (stinespring K)ᴴ) = krausMap K X := by
  rw [krausMap_apply]
  ext i j
  simp [mul_apply, stinespring, Matrix.sum_apply]

/-- **Stinespring dilation of a channel**, with environment `m × n`. -/
theorem IsChannel.exists_stinespring [DecidableEq m] [DecidableEq n] {Φ : MatMap m n}
    (h : IsChannel Φ) :
    ∃ V : Matrix (n × (m × n)) m ℂ, Vᴴ * V = 1 ∧ ∀ X, Φ X = traceRight (V * X * Vᴴ) := by
  obtain ⟨K, rfl, hK⟩ := (isChannel_iff_exists_kraus Φ).mp h
  exact ⟨stinespring K, stinespring_isometry hK, fun X => (traceRight_stinespring K X).symm⟩

omit [Fintype m] [Fintype n] in
theorem liftR_ptraceMap (Y : Matrix (R × (n × ι)) (R × (n × ι)) ℂ) :
    liftR R (ptraceMap n ι) Y =
      traceRight (Matrix.reindex (regAssoc R n ι).symm (regAssoc R n ι).symm Y) := by
  ext P Q; rfl

/-- **Entangled reference inputs.** For every input `X` on `R × m`,
`(id_R ⊗ Φ) X = Tr_E ((1 ⊗ V) X (1 ⊗ V)ᴴ)` (environment traced after reassociation). -/
theorem IsChannel.stinespring_ampliation [DecidableEq m] [DecidableEq n] [Fintype R]
    [DecidableEq R]
    {Φ : MatMap m n} (h : IsChannel Φ) :
    ∃ V : Matrix (n × (m × n)) m ℂ, Vᴴ * V = 1 ∧ ∀ X : Matrix (R × m) (R × m) ℂ,
      ShiQuantum.liftR R Φ X = traceRight (Matrix.reindex (regAssoc R n (m × n)).symm
        (regAssoc R n (m × n)).symm
        (((1 : Matrix R R ℂ) ⊗ₖ V) * X * ((1 : Matrix R R ℂ) ⊗ₖ V)ᴴ)) := by
  obtain ⟨V, hV, hΦ⟩ := h.exists_stinespring
  refine ⟨V, hV, fun X => ?_⟩
  have hcomp : Φ = ptraceMap n (m × n) ∘ₗ conjMap V := by
    apply LinearMap.ext; intro Y; exact hΦ Y
  rw [hcomp, liftR_comp, LinearMap.comp_apply, liftR_conjMap, liftR_ptraceMap]

/-! ## Unitary extension of an isometry -/

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Halmos's unitary dilation of `V : a ← b`, from `b ⊕ a` to `a ⊕ b`. -/
def halmos (V : Matrix a b ℂ) : Matrix (a ⊕ b) (b ⊕ a) ℂ :=
  fromBlocks V (1 - V * Vᴴ) 0 (-Vᴴ)

omit [Fintype a] [DecidableEq b] in
/-- On the embedded input, the dilation acts as `V`. -/
theorem halmos_inl (V : Matrix a b ℂ) (i : a) (c : b) :
    halmos V (Sum.inl i) (Sum.inl c) = V i c ∧ ∀ j : b, halmos V (Sum.inr j) (Sum.inl c) = 0 :=
  ⟨rfl, fun _ => rfl⟩

theorem halmos_unitary {V : Matrix a b ℂ} (hV : Vᴴ * V = 1) :
    (halmos V)ᴴ * halmos V = 1 ∧ halmos V * (halmos V)ᴴ = 1 := by
  have hP : V * Vᴴ * V = V := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hP' : Vᴴ * (V * Vᴴ) = Vᴴ := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hPP : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by rw [← Matrix.mul_assoc, hP]
  have hH : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  constructor
  · rw [halmos, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [hV]
    · simp [Matrix.mul_sub, hP']
    · rw [hH]; simp [Matrix.sub_mul, hP]
    · rw [hH]
      simp only [conjTranspose_neg, conjTranspose_conjTranspose, Matrix.neg_mul, Matrix.mul_neg,
        neg_neg]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]
      simp
  · rw [halmos, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, hH]
    congr 1
    · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]
      simp
    · simp [Matrix.sub_mul, hP]
    · simp [Matrix.mul_sub, hP']
    · simp [hV]

/-- The Halmos dilation with columns reordered: a square unitary on `a ⊕ b` whose block on the
embedded input `Sum.inr` is `V`. -/
def halmosSq (V : Matrix a b ℂ) : Matrix (a ⊕ b) (a ⊕ b) ℂ :=
  (halmos V).submatrix id (Equiv.sumComm a b)

omit [Fintype a] [DecidableEq b] in
theorem halmosSq_inr (V : Matrix a b ℂ) (i : a) (c : b) :
    halmosSq V (Sum.inl i) (Sum.inr c) = V i c := rfl

theorem halmosSq_mem_unitaryGroup {V : Matrix a b ℂ} (hV : Vᴴ * V = 1) :
    halmosSq V ∈ Matrix.unitaryGroup (a ⊕ b) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  have h := (halmos_unitary hV).1
  have e : halmosSq V = halmos V * permMat (Equiv.sumComm a b) := by
    ext i j
    rw [mul_apply, Finset.sum_eq_single (Equiv.sumComm a b j)]
    · simp [halmosSq, permMat_apply]
    · intro x _ hx
      rw [permMat_apply, if_neg, mul_zero]
      intro hx'; exact hx hx'.symm
    · simp
  rw [e, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (halmos V)ᴴ, h, Matrix.one_mul,
    permMat_conjTranspose_mul]

end ShiQuantum
