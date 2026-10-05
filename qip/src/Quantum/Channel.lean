/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.PartialTrace

/-!
# Q06 — quantum channels

A *matrix map* `MatMap m n` is a ℂ-linear map `Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ`.

* `liftR k Φ : MatMap (k × m) (k × n)` is `id_k ⊗ Φ`: it applies `Φ` to every `m`-block of a
  matrix on `k × m`, so it is `Φ` acting on the right register while the left register `k` is
  untouched.
* `IsPositiveMap Φ`: `Φ` maps PSD matrices to PSD matrices.
* `IsCP Φ` (**complete positivity**): `liftR k Φ` is positive for every finite type `k : Type`.
  This is strictly stronger than positivity; `IsCP.isPositiveMap` derives positivity from the
  case `k = Unit`.
* `IsTP Φ` (**trace preservation**) is a predicate on the same linear map:
  `trace (Φ X) = trace X` for every `X`.
* `IsChannel Φ := IsCP Φ ∧ IsTP Φ`. Channels map density operators to density operators.

Constructions proved CP here: the identity, composition, sums and nonnegative multiples,
conjugation `X ↦ V X Vᴴ` by any (rectangular) `V`, and hence Kraus maps `X ↦ ∑ Vᵢ X Vᵢᴴ`.
These maps are trace preserving when `∑ Vᵢᴴ Vᵢ = 1`. Concrete channels: unitary conjugation,
isometric embedding, the discard (trace) map, preparation of a fixed state, and complete
dephasing. Tensor products, local application and no-signalling are in `Quantum.ChannelTensor`.
-/

namespace ShiQuantum

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker

/-- ℂ-linear maps between square matrix spaces. -/
abbrev MatMap (m n : Type) := Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ

variable {k m n p : Type}

/-- The `(a, b)` block of a matrix on `k × m`. -/
def blockOf (X : Matrix (k × m) (k × m) ℂ) (a b : k) : Matrix m m ℂ :=
  Matrix.of fun i j => X (a, i) (b, j)

@[simp] theorem blockOf_apply (X : Matrix (k × m) (k × m) ℂ) (a b : k) (i j : m) :
    blockOf X a b i j = X (a, i) (b, j) := rfl

theorem blockOf_add (X Y : Matrix (k × m) (k × m) ℂ) (a b : k) :
    blockOf (X + Y) a b = blockOf X a b + blockOf Y a b := rfl

theorem blockOf_smul (c : ℂ) (X : Matrix (k × m) (k × m) ℂ) (a b : k) :
    blockOf (c • X) a b = c • blockOf X a b := rfl

/-- `id_k ⊗ Φ`: apply `Φ` to the right register, blockwise. -/
def liftR (k : Type) (Φ : MatMap m n) : MatMap (k × m) (k × n) where
  toFun X := Matrix.of fun P Q => Φ (blockOf X P.1 Q.1) P.2 Q.2
  map_add' X Y := by
    ext P Q
    simp [blockOf_add]
  map_smul' c X := by
    ext P Q
    simp [blockOf_smul]

@[simp] theorem liftR_apply (Φ : MatMap m n) (X : Matrix (k × m) (k × m) ℂ) (P Q : k × n) :
    liftR k Φ X P Q = Φ (blockOf X P.1 Q.1) P.2 Q.2 := rfl

/-- `Φ` maps PSD matrices to PSD matrices. -/
def IsPositiveMap [Fintype m] [Fintype n] (Φ : MatMap m n) : Prop :=
  ∀ X : Matrix m m ℂ, X.PosSemidef → (Φ X).PosSemidef

/-- **Complete positivity**: `id_k ⊗ Φ` is positive for every finite ancilla `k`. -/
def IsCP [Fintype m] [Fintype n] (Φ : MatMap m n) : Prop :=
  ∀ (k : Type) [Fintype k] [DecidableEq k], IsPositiveMap (liftR k Φ)

/-- **Trace preservation**, a property of the same linear map. -/
def IsTP [Fintype m] [Fintype n] (Φ : MatMap m n) : Prop := ∀ X : Matrix m m ℂ, trace (Φ X) = trace X

/-- A quantum channel: completely positive and trace preserving. -/
structure IsChannel [Fintype m] [Fintype n] (Φ : MatMap m n) : Prop where
  cp : IsCP Φ
  tp : IsTP Φ

/-! ## Algebra of `liftR` -/

theorem liftR_id : liftR k (LinearMap.id : MatMap m m) = LinearMap.id := by
  ext X P Q; rfl

theorem liftR_comp (Ψ : MatMap n p) (Φ : MatMap m n) :
    liftR k (Ψ ∘ₗ Φ) = liftR k Ψ ∘ₗ liftR k Φ := by
  ext X P Q; rfl

theorem liftR_add (Φ Ψ : MatMap m n) : liftR k (Φ + Ψ) = liftR k Φ + liftR k Ψ := by
  ext X P Q; rfl

theorem liftR_smul (c : ℂ) (Φ : MatMap m n) : liftR k (c • Φ) = c • liftR k Φ := by
  ext X P Q; rfl

variable [Fintype k] [Fintype m] [Fintype n] [Fintype p]

/-! ## Complete positivity implies positivity -/

theorem IsCP.isPositiveMap {Φ : MatMap m n} (h : IsCP Φ) : IsPositiveMap Φ := by
  intro X hX
  have hX' : (X.submatrix (Prod.snd : Unit × m → m) Prod.snd).PosSemidef := hX.submatrix _
  have := (h Unit _ hX').submatrix (fun i : n => ((), i))
  convert this using 1
  ext i j; rfl

/-- Channels map density operators to density operators. -/
theorem IsChannel.map_density {Φ : MatMap m n} (h : IsChannel Φ) {ρ : Matrix m m ℂ}
    (hρ : IsDensity ρ) : IsDensity (Φ ρ) :=
  ⟨h.cp.isPositiveMap ρ hρ.posSemidef, by rw [h.tp, hρ.trace_eq_one]⟩

/-! ## Identity, composition, sums -/

theorem isCP_id : IsCP (LinearMap.id : MatMap m m) := by
  intro k _ _ X hX
  rw [liftR_id]; exact hX

theorem isTP_id : IsTP (LinearMap.id : MatMap m m) := fun _ => rfl

theorem isChannel_id : IsChannel (LinearMap.id : MatMap m m) := ⟨isCP_id, isTP_id⟩

theorem IsCP.comp {Ψ : MatMap n p} {Φ : MatMap m n} (hΨ : IsCP Ψ) (hΦ : IsCP Φ) :
    IsCP (Ψ ∘ₗ Φ) := by
  intro k _ _ X hX
  rw [liftR_comp]
  exact hΨ k _ (hΦ k _ hX)

theorem IsTP.comp {Ψ : MatMap n p} {Φ : MatMap m n} (hΨ : IsTP Ψ) (hΦ : IsTP Φ) :
    IsTP (Ψ ∘ₗ Φ) := fun X => by
  rw [LinearMap.comp_apply, hΨ, hΦ]

theorem IsChannel.comp {Ψ : MatMap n p} {Φ : MatMap m n} (hΨ : IsChannel Ψ)
    (hΦ : IsChannel Φ) : IsChannel (Ψ ∘ₗ Φ) :=
  ⟨hΨ.cp.comp hΦ.cp, hΨ.tp.comp hΦ.tp⟩

theorem IsCP.add {Φ Ψ : MatMap m n} (hΦ : IsCP Φ) (hΨ : IsCP Ψ) : IsCP (Φ + Ψ) := by
  intro k _ _ X hX
  rw [liftR_add, LinearMap.add_apply]
  exact (hΦ k _ hX).add (hΨ k _ hX)

theorem isCP_zero : IsCP (0 : MatMap m n) := by
  intro k _ _ X _
  have : liftR k (0 : MatMap m n) = 0 := by ext X P Q; rfl
  rw [this, LinearMap.zero_apply]
  exact PosSemidef.zero

theorem IsCP.smul {Φ : MatMap m n} (hΦ : IsCP Φ) {r : ℝ} (hr : 0 ≤ r) :
    IsCP ((r : ℂ) • Φ) := by
  intro k _ _ X hX
  rw [liftR_smul, LinearMap.smul_apply]
  have := (hΦ k _ hX).smul hr
  rwa [← Complex.coe_smul] at this

theorem isCP_sum {ι : Type*} (s : Finset ι) {Φ : ι → MatMap m n} (h : ∀ i ∈ s, IsCP (Φ i)) :
    IsCP (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isCP_zero : IsCP (0 : MatMap m n))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## Conjugation and Kraus maps -/

/-- Conjugation `X ↦ V X Vᴴ` by a (possibly rectangular) matrix `V : n ← m`. -/
def conjMap (V : Matrix n m ℂ) : MatMap m n where
  toFun X := V * X * Vᴴ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

omit [Fintype n] in
@[simp] theorem conjMap_apply (V : Matrix n m ℂ) (X : Matrix m m ℂ) : conjMap V X = V * X * Vᴴ :=
  rfl

omit [Fintype n] in
theorem one_kronecker_mul_apply {q : Type*} [DecidableEq k] (V : Matrix n m ℂ)
    (X : Matrix (k × m) q ℂ) (a : k) (i : n) (Q : q) :
    (((1 : Matrix k k ℂ) ⊗ₖ V) * X) (a, i) Q = ∑ l, V i l * X (a, l) Q := by
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro r _ hr
    simp [one_apply_ne (Ne.symm hr)]
  · simp

omit [Fintype n] in
theorem mul_one_kronecker_apply {q : Type*} [DecidableEq k] (W : Matrix m n ℂ)
    (X : Matrix q (k × m) ℂ) (P : q) (b : k) (j : n) :
    (X * ((1 : Matrix k k ℂ) ⊗ₖ W)) P (b, j) = ∑ l, X P (b, l) * W l j := by
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro r _ hr
    simp [one_apply_ne hr]
  · simp

omit [Fintype n] in
/-- `id_k ⊗ (V · Vᴴ)` is conjugation by `1 ⊗ V`. -/
theorem liftR_conjMap [DecidableEq k] (V : Matrix n m ℂ) (X : Matrix (k × m) (k × m) ℂ) :
    liftR k (conjMap V) X = ((1 : Matrix k k ℂ) ⊗ₖ V) * X * ((1 : Matrix k k ℂ) ⊗ₖ V)ᴴ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [conjTranspose_kronecker, conjTranspose_one, mul_one_kronecker_apply]
  simp only [one_kronecker_mul_apply]
  simp only [liftR_apply, conjMap_apply, mul_apply, blockOf_apply]

theorem isCP_conjMap (V : Matrix n m ℂ) : IsCP (conjMap V) := by
  intro k _ _ X hX
  rw [liftR_conjMap]
  exact hX.mul_mul_conjTranspose_same _

/-- Conjugation by an isometry (`Vᴴ V = 1`) is trace preserving. -/
theorem isTP_conjMap [DecidableEq m] {V : Matrix n m ℂ} (h : Vᴴ * V = 1) : IsTP (conjMap V) :=
  fun X => by rw [conjMap_apply, trace_mul_cycle, h, Matrix.one_mul]

theorem isChannel_conjMap [DecidableEq m] {V : Matrix n m ℂ} (h : Vᴴ * V = 1) :
    IsChannel (conjMap V) :=
  ⟨isCP_conjMap V, isTP_conjMap h⟩

/-- Unitary conjugation is a channel. -/
theorem isChannel_unitary [DecidableEq m] {U : Matrix m m ℂ} (hU : U ∈ Matrix.unitaryGroup m ℂ) :
    IsChannel (conjMap U) :=
  isChannel_conjMap (by rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU)

/-! ## Kraus maps -/

/-- The Kraus map `X ↦ ∑ i, V i * X * (V i)ᴴ`. -/
def krausMap {ι : Type*} [Fintype ι] (V : ι → Matrix n m ℂ) : MatMap m n := ∑ i, conjMap (V i)

omit [Fintype n] in
theorem krausMap_apply {ι : Type*} [Fintype ι] (V : ι → Matrix n m ℂ) (X : Matrix m m ℂ) :
    krausMap V X = ∑ i, V i * X * (V i)ᴴ := by
  simp [krausMap, LinearMap.sum_apply]

theorem isCP_krausMap {ι : Type*} [Fintype ι] (V : ι → Matrix n m ℂ) : IsCP (krausMap V) :=
  isCP_sum _ fun i _ => isCP_conjMap (V i)

theorem isTP_krausMap [DecidableEq m] {ι : Type*} [Fintype ι] {V : ι → Matrix n m ℂ}
    (h : ∑ i, (V i)ᴴ * V i = 1) : IsTP (krausMap V) := fun X => by
  rw [krausMap_apply, trace_sum]
  rw [Finset.sum_congr rfl fun i _ => trace_mul_cycle (V i) X (V i)ᴴ, ← trace_sum,
    ← Finset.sum_mul, h, Matrix.one_mul]

theorem isChannel_krausMap [DecidableEq m] {ι : Type*} [Fintype ι] {V : ι → Matrix n m ℂ}
    (h : ∑ i, (V i)ᴴ * V i = 1) : IsChannel (krausMap V) :=
  ⟨isCP_krausMap V, isTP_krausMap h⟩

/-! ## Discarding a register -/

/-- Discard a register: `X ↦ trace X` on the one-dimensional register `Unit`. -/
def discardMap (m : Type) [Fintype m] : MatMap m Unit where
  toFun X := Matrix.of fun _ _ => trace X
  map_add' X Y := by ext; simp [trace_add]
  map_smul' c X := by ext; simp [trace_smul]

omit [Fintype k] in
/-- `id_k ⊗ discard` is the partial trace. -/
theorem liftR_discardMap (X : Matrix (k × m) (k × m) ℂ) :
    liftR k (discardMap m) X = (traceRight X).submatrix Prod.fst Prod.fst := by
  ext P Q; simp [discardMap, trace]

theorem isChannel_discardMap : IsChannel (discardMap m) := by
  refine ⟨fun k _ _ X hX => ?_, fun X => by simp [discardMap, trace]⟩
  rw [liftR_discardMap]
  exact (posSemidef_traceRight hX).submatrix _

/-! ## Preparing a state -/

/-- Prepare `σ` from the one-dimensional register: `x ↦ x () () • σ`. -/
def prepMap (σ : Matrix n n ℂ) : MatMap Unit n where
  toFun x := x () () • σ
  map_add' x y := by rw [Matrix.add_apply, add_smul]
  map_smul' c x := by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]; rfl

omit [Fintype k] [Fintype n] in
theorem liftR_prepMap (σ : Matrix n n ℂ) (X : Matrix (k × Unit) (k × Unit) ℂ) :
    liftR k (prepMap σ) X = X.submatrix (fun a => (a, ())) (fun a => (a, ())) ⊗ₖ σ := by
  ext P Q; simp [prepMap]

theorem isChannel_prepMap {σ : Matrix n n ℂ} (hσ : IsDensity σ) : IsChannel (prepMap σ) := by
  refine ⟨fun k _ _ X hX => ?_, fun x => ?_⟩
  · rw [liftR_prepMap]
    exact (hX.submatrix _).kronecker hσ.posSemidef
  · change trace (x () () • σ) = trace x
    rw [trace_smul, hσ.trace_eq_one, smul_eq_mul, mul_one]
    simp [trace]

/-! ## Complete dephasing -/

/-- Complete dephasing in the computational basis: keep only the diagonal. -/
def dephase (m : Type) [Fintype m] [DecidableEq m] : MatMap m m where
  toFun X := diagonal fun i => X i i
  map_add' X Y := by ext a b; simp [diagonal_apply]; split_ifs <;> simp
  map_smul' c X := by ext a b; simp [diagonal_apply]

/-- Dephasing is the Kraus map of the basis projectors. -/
theorem dephase_eq_krausMap [DecidableEq m] :
    dephase m = krausMap (fun i : m => basisEffect (· = i)) := by
  apply LinearMap.ext
  intro X
  rw [krausMap_apply]
  ext a b
  simp only [dephase, LinearMap.coe_mk, AddHom.coe_mk, basisEffect, diagonal_conjTranspose,
    diagonal_mul, mul_diagonal, Matrix.sum_apply, diagonal_apply, Pi.star_apply]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab]

theorem isChannel_dephase [DecidableEq m] : IsChannel (dephase m) := by
  refine ⟨?_, fun X => by simp [dephase, trace]⟩
  rw [dephase_eq_krausMap]
  exact isCP_krausMap _

/-! ## Instruments -/

/-- An instrument: outcome-indexed CP maps whose sum is trace preserving. -/
structure IsInstrument {ι : Type*} [Fintype ι] (Φ : ι → MatMap m n) : Prop where
  cp : ∀ i, IsCP (Φ i)
  tp : IsTP (∑ i, Φ i)

theorem IsInstrument.isChannel_sum {ι : Type*} [Fintype ι] {Φ : ι → MatMap m n}
    (h : IsInstrument Φ) : IsChannel (∑ i, Φ i) :=
  ⟨isCP_sum _ fun i _ => h.cp i, h.tp⟩

/-- Outcome probabilities `Re (trace (Φ i ρ))` are nonnegative ... -/
theorem IsInstrument.prob_nonneg {ι : Type*} [Fintype ι] {Φ : ι → MatMap m n}
    (h : IsInstrument Φ) {ρ : Matrix m m ℂ} (hρ : IsDensity ρ) (i : ι) :
    0 ≤ (trace (Φ i ρ)).re :=
  psd_trace_re_nonneg ((h.cp i).isPositiveMap ρ hρ.posSemidef)

/-- ... and sum to one. -/
theorem IsInstrument.sum_prob {ι : Type*} [Fintype ι] {Φ : ι → MatMap m n}
    (h : IsInstrument Φ) {ρ : Matrix m m ℂ} (hρ : IsDensity ρ) :
    ∑ i, (trace (Φ i ρ)).re = 1 := by
  have := h.tp ρ
  rw [LinearMap.sum_apply, trace_sum, hρ.trace_eq_one] at this
  rw [← Complex.re_sum, this, Complex.one_re]

/-- Measuring in the computational basis, keeping the post-measurement state. -/
theorem isInstrument_basis [DecidableEq m] :
    IsInstrument (fun i : m => conjMap (basisEffect (· = i))) :=
  ⟨fun i => isCP_conjMap _, by
    have h : (∑ i : m, conjMap (basisEffect (· = i))) = dephase m := dephase_eq_krausMap.symm
    rw [h]; exact isChannel_dephase.tp⟩

/-! ## Positivity is weaker than complete positivity -/

/-- The transpose map. -/
def transposeMap (m : Type) : MatMap m m where
  toFun X := Xᵀ
  map_add' X Y := transpose_add X Y
  map_smul' c X := transpose_smul c X

theorem transposeMap_isPositiveMap : IsPositiveMap (transposeMap m) :=
  fun _ hX => hX.transpose

/-- The transpose is positive but **not** completely positive: on the unnormalized Bell
matrix its ampliation has the negative expectation `-2` in the vector `|01⟩ - |10⟩`. -/
theorem not_isCP_transposeMap : ¬ IsCP (transposeMap Bool) := by
  intro h
  let v : Bool × Bool → ℂ := fun P => if P.1 = P.2 then 1 else 0
  let w : Bool × Bool → ℂ := fun P =>
    if P = (false, true) then 1 else if P = (true, false) then -1 else 0
  have hX := h Bool (vecMulVec v (star v)) (posSemidef_vecMulVec_self_star v)
  have hw := hX.dotProduct_mulVec_nonneg w
  have : star w ⬝ᵥ (liftR Bool (transposeMap Bool) (vecMulVec v (star v)) *ᵥ w) = -2 := by
    simp [dotProduct, mulVec, Fintype.sum_prod_type, v, w, transposeMap, vecMulVec_apply]
    norm_num
  rw [this] at hw
  have := (Complex.nonneg_iff.mp hw).1
  norm_num at this

end ShiQuantum
