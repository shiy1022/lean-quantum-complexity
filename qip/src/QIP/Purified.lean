/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Tester
import QIP.ValidGates
import Quantum.Dilation
import Quantum.Purification

/-!
# Q17 — purified strategies

An **isometric strategy** (`IsoStrategy X Y r`) starts its memory in a pure state and performs
every turn by an isometry `V k : X k × M k → Y k × M (k + 1)`. `IsoStrategy.toOp` views it as
an operational strategy.

**`exists_iso_of_op`**: every operational strategy `S` has an isometric strategy with the same
strategy operators, `stratOp (T.toOp) k = stratOp S k` for `k ≤ r`. The memory is enlarged by
a purifying reference for the initial state and the Stinespring environments of all turns so
far (`envT`), and each turn is the Stinespring isometry tensored with the identity on the
accumulated environment. Tracing out the environment recovers the original link-product
states (`redE_memState`).

**`exists_isoProver`**: for a verifier description `d`, every prover has an isometric prover
with the same acceptance probability.

On the verifier side no normalization is needed: by definition (`QIP.Execution`) verifiers are
unitary circuits on wires that all start in `|0⟩`, with one final measured output wire.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

/-- An isometric strategy: pure initial memory, isometric turns. -/
structure IsoStrategy (X Y : ℕ → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (X i)] (r : ℕ) where
  M : ℕ → Type
  [memFintype : ∀ k, Fintype (M k)]
  [memDecEq : ∀ k, DecidableEq (M k)]
  init : M 0 → ℂ
  init_density : IsDensity (pureState init)
  V : ∀ k, Matrix (Y k × M (k + 1)) (X k × M k) ℂ
  V_iso : ∀ k < r, (V k)ᴴ * V k = 1

attribute [instance] IsoStrategy.memFintype IsoStrategy.memDecEq

variable {r : ℕ}

/-- An isometric strategy as an operational strategy. -/
@[reducible] noncomputable def IsoStrategy.toOp (T : IsoStrategy X Y r) : OpStrategy X Y r where
  M := T.M
  init := pureState T.init
  init_density := T.init_density
  act k := conjMap (T.V k)
  act_channel k hk := isChannel_conjMap (T.V_iso k hk)

/-! ## The dilation -/

section Dilation

variable (S : OpStrategy X Y r)

/-- The accumulated environment: a purifying reference, then the Stinespring environment of
each turn. -/
def envT : ℕ → Type
  | 0 => S.M 0
  | k + 1 => envT k × ((X k × S.M k) × (Y k × S.M (k + 1)))

instance envT_fintype : ∀ k, Fintype (envT S k)
  | 0 => inferInstanceAs (Fintype (S.M 0))
  | k + 1 => @instFintypeProd _ _ (envT_fintype k) inferInstance

instance envT_decEq : ∀ k, DecidableEq (envT S k)
  | 0 => inferInstanceAs (DecidableEq (S.M 0))
  | k + 1 => @instDecidableEqProd _ _ (envT_decEq k) inferInstance

/-- The Stinespring isometry of turn `k` (an arbitrary matrix beyond the last turn). -/
noncomputable def stin (k : ℕ) :
    Matrix ((Y k × S.M (k + 1)) × ((X k × S.M k) × (Y k × S.M (k + 1)))) (X k × S.M k) ℂ :=
  if h : k < r then Classical.choose (S.act_channel k h).exists_stinespring else 0

theorem stin_spec {k : ℕ} (hk : k < r) : (stin S k)ᴴ * stin S k = 1 ∧
    ∀ A, S.act k A = traceRight (stin S k * A * (stin S k)ᴴ) := by
  simp only [stin, dif_pos hk]
  exact Classical.choose_spec (S.act_channel k hk).exists_stinespring

/-- The environment of one turn. -/
abbrev envStep (k : ℕ) : Type := (X k × S.M k) × (Y k × S.M (k + 1))

/-- Output indices of a dilated turn, regrouped. -/
def dilOut (k : ℕ) :
    Y k × (S.M (k + 1) × envT S (k + 1)) ≃ ((Y k × S.M (k + 1)) × envStep S k) × envT S k where
  toFun p := (((p.1, p.2.1), (p.2.2 : envT S k × envStep S k).2), (p.2.2 : envT S k × envStep S k).1)
  invFun q := (q.1.1.1, (q.1.1.2, ((q.2, q.1.2) : envT S k × envStep S k)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dilated turn: the Stinespring isometry, the identity on the accumulated environment. -/
noncomputable def dilV (k : ℕ) :
    Matrix (Y k × (S.M (k + 1) × envT S (k + 1))) (X k × (S.M k × envT S k)) ℂ :=
  (stin S k ⊗ₖ (1 : Matrix (envT S k) (envT S k) ℂ)).submatrix (dilOut S k)
    (Equiv.prodAssoc (X k) (S.M k) (envT S k)).symm

theorem dilV_iso {k : ℕ} (hk : k < r) : (dilV S k)ᴴ * dilV S k = 1 := by
  rw [dilV, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
    conjTranspose_one, ← mul_kronecker_mul, (stin_spec S hk).1, Matrix.one_mul, one_kronecker_one,
    submatrix_one_equiv]

/-- **The dilated strategy.** -/
noncomputable def dilate : IsoStrategy X Y r where
  M k := S.M k × envT S k
  init := purify S.init
  init_density := (purify_isPurification S.init_density.posSemidef).isDensity S.init_density
  V := dilV S
  V_iso _ hk := dilV_iso S hk

/-- Trace out the environment. -/
def redE {H Mm E : Type} [Fintype E] (R : Matrix (H × (Mm × E)) (H × (Mm × E)) ℂ) :
    Matrix (H × Mm) (H × Mm) ℂ :=
  Matrix.of fun p q => ∑ e, R (p.1, (p.2, e)) (q.1, (q.2, e))

end Dilation

/-! ## Tracing out the environment -/

section General

variable {H Xx Yy Mm Mm' E Env : Type} [Fintype H] [Fintype Xx] [Fintype Yy] [Fintype Mm]
  [Fintype Mm'] [Fintype E] [Fintype Env] [DecidableEq Xx] [DecidableEq E]

/-- `Yy × (Mm' × (E × Env)) ≃ ((Yy × Mm') × Env) × E`. -/
def regroupOut (Yy Mm' E Env : Type) : Yy × (Mm' × (E × Env)) ≃ ((Yy × Mm') × Env) × E where
  toFun p := (((p.1, p.2.1), p.2.2.2), p.2.2.1)
  invFun q := (q.1.1.1, (q.1.1.2, (q.2, q.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A Stinespring isometry `B` with the identity on `E`, regrouped. -/
def dilOf (B : Matrix ((Yy × Mm') × Env) (Xx × Mm) ℂ) :
    Matrix (Yy × (Mm' × (E × Env))) (Xx × (Mm × E)) ℂ :=
  (B ⊗ₖ (1 : Matrix E E ℂ)).submatrix (regroupOut Yy Mm' E Env) (Equiv.prodAssoc Xx Mm E).symm

set_option linter.unusedSectionVars false in
/-- **Tracing out the environment of one dilated turn.** -/
theorem redE_linkStep (Φ : MatMap (Xx × Mm) (Yy × Mm'))
    (B : Matrix ((Yy × Mm') × Env) (Xx × Mm) ℂ) (hB : ∀ A, Φ A = traceRight (B * A * Bᴴ))
    (R : Matrix (H × (Mm × E)) (H × (Mm × E)) ℂ) (h h' : H) (x x' : Xx) (y y' : Yy)
    (m m' : Mm') :
    ∑ q : E × Env, linkStep (conjMap (dilOf (E := E) B)) R ((h, x), (y, (m, q)))
        ((h', x'), (y', (m', q))) =
      linkStep Φ (redE R) ((h, x), (y, m)) ((h', x'), (y', m')) := by
  rw [linkStep_apply, hB]
  simp only [linkStep_apply]
  set A := Matrix.single x x' (1 : ℂ) ⊗ₖ memBlock R h h'
  have hA : traceRight (A.submatrix (Equiv.prodAssoc Xx Mm E) (Equiv.prodAssoc Xx Mm E)) =
      Matrix.single x x' (1 : ℂ) ⊗ₖ memBlock (redE R) h h' := by
    ext ⟨a, n⟩ ⟨b, n'⟩
    simp only [traceRight_apply, submatrix_apply, Equiv.prodAssoc_apply, A, kroneckerMap_apply,
      memBlock, redE, of_apply, Finset.mul_sum]
  have e1 : conjMap (dilOf (E := E) B) A =
      ((B ⊗ₖ (1 : Matrix E E ℂ)) * A.submatrix (Equiv.prodAssoc Xx Mm E)
        (Equiv.prodAssoc Xx Mm E) * (B ⊗ₖ (1 : Matrix E E ℂ))ᴴ).submatrix
          (regroupOut Yy Mm' E Env) (regroupOut Yy Mm' E Env) := by
    rw [conjMap_apply, dilOf, conjTranspose_submatrix,
      show A = (A.submatrix (Equiv.prodAssoc Xx Mm E) (Equiv.prodAssoc Xx Mm E)).submatrix
        (Equiv.prodAssoc Xx Mm E).symm (Equiv.prodAssoc Xx Mm E).symm by simp,
      submatrix_mul_equiv, submatrix_mul_equiv]
    simp
  rw [e1]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [submatrix_apply, regroupOut, Equiv.coe_fn_mk]
  have e2 := traceRight_local B (A.submatrix (Equiv.prodAssoc Xx Mm E) (Equiv.prodAssoc Xx Mm E))
    Bᴴ (β := E)
  rw [← conjTranspose_one, ← conjTranspose_kronecker, conjTranspose_one] at e2
  rw [← hA, ← e2]
  simp only [traceRight_apply]

end General

section Dilation2

variable (S : OpStrategy X Y r)

/-- **The dilated strategy has the same link-product states, up to the environment.** -/
theorem redE_memState : ∀ k ≤ r, redE (memState (dilate S).toOp k) = memState S k
  | 0, _ => by
    ext ⟨u, m⟩ ⟨u', m'⟩
    have h := congrFun (congrFun (purify_isPurification S.init_density.posSemidef) m) m'
    simp only [traceRight_apply, pureState, vecMulVec_apply, Pi.star_apply] at h
    simp only [redE, of_apply, memState, reindex_apply, IsoStrategy.toOp, dilate, pureState]
    exact h
  | k + 1, hk => by
    have ih := redE_memState k (by omega)
    obtain ⟨-, hB⟩ := stin_spec S (k := k) (by omega)
    ext ⟨⟨⟨h, x⟩, y⟩, m⟩ ⟨⟨⟨h', x'⟩, y'⟩, m'⟩
    change ∑ q : envT S k × envStep S k, linkStep (conjMap (dilOf (E := envT S k) (stin S k)))
        (memState (dilate S).toOp k) ((h, x), (y, (m, q))) ((h', x'), (y', (m', q))) = _
    refine (redE_linkStep (S.act k) (stin S k) hB (memState (dilate S).toOp k) h h' x x' y y'
      m m').trans ?_
    rw [ih]
    rfl

/-- **Purification preserves the strategy operator.** -/
theorem stratOp_dilate {k : ℕ} (hk : k ≤ r) : stratOp (dilate S).toOp k = stratOp S k := by
  ext a b
  change ∑ p : S.M k × envT S k, memState (dilate S).toOp k (a, p) (b, p) = _
  rw [stratOp, traceRight_apply, ← redE_memState S k hk, Fintype.sum_prod_type]
  rfl

theorem exists_iso_of_op : ∃ T : IsoStrategy X Y r, ∀ k ≤ r, stratOp T.toOp k = stratOp S k :=
  ⟨dilate S, fun _ hk => stratOp_dilate S hk⟩

end Dilation2

/-- **Every prover has an isometric prover with the same acceptance probability.** -/
theorem exists_isoProver {d : Desc} (P : Prover d) :
    ∃ T : IsoStrategy (Reg d) (Reg d) d.numMsgs, accept T.toOp = accept P := by
  obtain ⟨T, hT⟩ := exists_iso_of_op P
  exact ⟨T, by rw [accept_eq_pairing, accept_eq_pairing, hT _ le_rfl]⟩

end ShiQIP
