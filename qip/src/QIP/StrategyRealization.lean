/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.StrategyOperator

/-!
# Q19 (forward direction) — operational strategies induce strategy operators

An **operational strategy** (`OpStrategy X Y r`) has private memory registers `M k` of arbitrary
finite type, an initial memory density operator, and for each turn `k < r` a channel
`act k : X k × M k → Y k × M (k + 1)`. The input register is received, the output register is
sent, and the memory is kept.

**Link-product recursion.** `memState k` is an operator on `Hist X Y k × M k`:

* `memState 0 = init` (with `Hist 0 = Unit`);
* `memState (k + 1)` is obtained by tensoring `memState k` with the unnormalized maximally
  entangled `|Ω⟩⟨Ω|` on `X k × X k`, then applying `act k` to the second copy of `X k` together
  with the memory (`linkStep`).

The strategy operator is `stratOp k = Tr_{M k} (memState k)`.

* `memState_posSemidef`: every `memState k` is PSD (complete positivity).
* **`opStrategy_isStrategy`**: `stratOp` satisfies `IsStrategy r`, i.e. `Q 0 = 1` and
  `Tr_{Y k} Q (k + 1) = Q k ⊗ 1_{X k}`. Trace preservation of each turn, through `traceRight_liftR`
  (no-signalling), is what makes the causal equations hold.

The converse — every causal operator is realized by an operational strategy with bounded
memory — is the remaining part of Q19.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

/-- An operational `r`-turn strategy with arbitrary finite memory. -/
structure OpStrategy (X Y : ℕ → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] (r : ℕ) where
  M : ℕ → Type
  [memFintype : ∀ k, Fintype (M k)]
  [memDecEq : ∀ k, DecidableEq (M k)]
  init : Matrix (M 0) (M 0) ℂ
  init_density : IsDensity init
  act : ∀ k, MatMap (X k × M k) (Y k × M (k + 1))
  act_channel : ∀ k < r, IsChannel (act k)

attribute [instance] OpStrategy.memFintype OpStrategy.memDecEq

/-- `((h, m), (x, x')) ↦ ((h, x), (x', m))`. -/
def linkEquiv (H Mm Xx : Type) : (H × Mm) × (Xx × Xx) ≃ (H × Xx) × (Xx × Mm) where
  toFun p := ((p.1.1, p.2.1), (p.2.2, p.1.2))
  invFun q := ((q.1.1, q.2.2), (q.1.2, q.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- One turn of the link product: tensor with `|Ω⟩⟨Ω|_X`, then apply `Φ` to `X' × M`. -/
noncomputable def linkStep {H Xx Yy Mm Mm' : Type} [Fintype H] [Fintype Xx] [DecidableEq Xx]
    [Fintype Mm] (Φ : MatMap (Xx × Mm) (Yy × Mm')) (R : Matrix (H × Mm) (H × Mm) ℂ) :
    Matrix ((H × Xx) × Yy × Mm') ((H × Xx) × Yy × Mm') ℂ :=
  liftR (H × Xx) Φ (Matrix.reindex (linkEquiv H Mm Xx) (linkEquiv H Mm Xx)
    (R ⊗ₖ vecMulVec (omegaVec Xx) (star (omegaVec Xx))))

theorem linkStep_posSemidef {H Xx Yy Mm Mm' : Type} [Fintype H] [DecidableEq H] [Fintype Xx]
    [DecidableEq Xx] [Fintype Mm] [DecidableEq Mm] [Fintype Yy] [Fintype Mm']
    {Φ : MatMap (Xx × Mm) (Yy × Mm')} (hΦ : IsCP Φ) {R : Matrix (H × Mm) (H × Mm) ℂ}
    (hR : R.PosSemidef) : (linkStep Φ R).PosSemidef := by
  apply hΦ
  rw [reindex_apply]
  exact (posSemidef_submatrix_equiv _).mpr (hR.kronecker (posSemidef_vecMulVec_self_star _))

/-- The partial trace of `|Ω⟩⟨Ω|` over one copy is the identity. -/
theorem traceRight_link {H Xx Mm : Type} [Fintype H] [Fintype Xx] [DecidableEq Xx] [Fintype Mm]
    (R : Matrix (H × Mm) (H × Mm) ℂ) :
    traceRight (Matrix.reindex (linkEquiv H Mm Xx) (linkEquiv H Mm Xx)
      (R ⊗ₖ vecMulVec (omegaVec Xx) (star (omegaVec Xx)))) = traceRight R ⊗ₖ (1 : Matrix Xx Xx ℂ) := by
  ext ⟨h, x⟩ ⟨h', x'⟩
  rw [traceRight_apply, kronecker_apply, traceRight_apply, Fintype.sum_prod_type]
  change ∑ x'' : Xx, ∑ m : Mm, R (h, m) (h', m) *
    vecMulVec (omegaVec Xx) (star (omegaVec Xx)) (x, x'') (x', x'') = _
  simp only [vecMulVec_apply, omegaVec, Pi.star_apply, one_apply]
  rw [Finset.sum_eq_single x]
  · by_cases hx : x = x'
    · subst hx; simp
    · simp [hx, Ne.symm hx]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Tracing out `Y × M'` after one turn: trace preservation removes the turn. -/
theorem traceRight_linkStep {H Xx Yy Mm Mm' : Type} [Fintype H] [Fintype Xx] [DecidableEq Xx]
    [Fintype Mm] [Fintype Yy] [Fintype Mm'] {Φ : MatMap (Xx × Mm) (Yy × Mm')} (hΦ : IsTP Φ)
    (R : Matrix (H × Mm) (H × Mm) ℂ) :
    traceRight (linkStep Φ R) = traceRight R ⊗ₖ (1 : Matrix Xx Xx ℂ) := by
  rw [linkStep, traceRight_liftR hΦ, traceRight_link]

variable {r : ℕ}

/-- The state of the history together with the memory after `k` turns. -/
noncomputable def memState (S : OpStrategy X Y r) :
    ∀ k, Matrix (Hist X Y k × S.M k) (Hist X Y k × S.M k) ℂ
  | 0 => Matrix.reindex (Equiv.punitProd (S.M 0)).symm (Equiv.punitProd (S.M 0)).symm S.init
  | k + 1 =>
    Matrix.reindex (Equiv.prodAssoc (Hist X Y k × X k) (Y k) (S.M (k + 1))).symm
      (Equiv.prodAssoc (Hist X Y k × X k) (Y k) (S.M (k + 1))).symm
      (linkStep (S.act k) (memState S k))

/-- The strategy operator: trace out the memory. -/
noncomputable def stratOp (S : OpStrategy X Y r) (k : ℕ) :
    Matrix (Hist X Y k) (Hist X Y k) ℂ :=
  traceRight (memState S k)

theorem memState_posSemidef (S : OpStrategy X Y r) : ∀ k ≤ r, (memState S k).PosSemidef
  | 0, _ => by
    rw [memState, reindex_apply]
    exact (posSemidef_submatrix_equiv _).mpr S.init_density.posSemidef
  | k + 1, hk => by
    rw [memState, reindex_apply]
    exact (posSemidef_submatrix_equiv _).mpr
      (linkStep_posSemidef (S.act_channel k (by omega)).cp (memState_posSemidef S k (by omega)))

omit [∀ i, DecidableEq (Y i)] in
theorem stratOp_succ (S : OpStrategy X Y r) {k : ℕ} (hk : k < r) :
    traceRight (stratOp S (k + 1) :
      Matrix ((Hist X Y k × X k) × Y k) ((Hist X Y k × X k) × Y k) ℂ) =
      stratOp S k ⊗ₖ (1 : Matrix (X k) (X k) ℂ) := by
  have h := traceRight_linkStep (S.act_channel k hk).tp (memState S k)
  have e : traceRight (stratOp S (k + 1) :
      Matrix ((Hist X Y k × X k) × Y k) ((Hist X Y k × X k) × Y k) ℂ) =
      traceRight (linkStep (S.act k) (memState S k)) := by
    ext a b
    change ∑ y : Y k, ∑ mm : S.M (k + 1),
      linkStep (S.act k) (memState S k) (a, (y, mm)) (b, (y, mm)) = _
    rw [traceRight_apply, Fintype.sum_prod_type]
  rw [e, h]; rfl

/-- **Operational strategies induce causal strategy operators.** -/
theorem opStrategy_isStrategy (S : OpStrategy X Y r) : IsStrategy r (stratOp S) where
  zero := by
    ext a b
    have hab : a = b := Subsingleton.elim (α := Unit) a b
    subst hab
    have := S.init_density.trace_eq_one
    simp only [trace, diag_apply] at this
    simp only [stratOp, memState, reindex_apply, one_apply_eq]
    exact this
  posSemidef k hk := posSemidef_traceRight (memState_posSemidef S k hk)
  causal k hk := stratOp_succ S hk

end ShiQIP
