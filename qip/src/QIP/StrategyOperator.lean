/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Quantum.Kraus

/-!
# Q18 — causal strategy operators

A prover **turn** `k` receives an input register `X k` and produces an output register `Y k`.
Turns are not messages: one turn consumes one incoming and produces one outgoing register, and
a register may be one-dimensional (`Unit`). In particular, an initial state preparation is a turn
whose input has dimension one.

**Register order (frozen).** The history after `k` turns is

  `Hist X Y 0 = Unit`,  `Hist X Y (k + 1) = (Hist X Y k × X k) × Y k`,

so each turn appends its input and then its output on the right.

A `k`-turn strategy operator is a family `Q j` (`j ≤ k`) of PSD matrices on `Hist X Y j` with

  `Q 0 = 1`,  `Tr_{Y j} (Q (j + 1)) = Q j ⊗ 1_{X j}`   (`IsStrategy`).

With this order the causal equation is exactly `traceRight` of `Quantum.PartialTrace`: no
reindexing is needed.

* `IsStrategy.trace_eq`: `trace (Q j) = ∏_{i < j} card (X i)`. A strategy operator is generally
  **not** trace one.
* `IsStrategy.prefix_unique`: the final operator determines all prefixes (when the inputs are
  nonempty).
* `isStrategy_one_iff_choi`: one-turn strategies are exactly the (reindexed) Choi matrices of
  channels `X 0 → Y 0`.
* `isStrategy_one_prep_iff`: with input `Unit`, one-turn strategies are exactly density
  operators on the output, i.e. state preparations.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable (X Y : ℕ → Type)

/-- The history register after `k` turns. -/
def Hist : ℕ → Type
  | 0 => Unit
  | k + 1 => (Hist k × X k) × Y k

variable {X Y}
variable [hX : ∀ i, Fintype (X i)] [hY : ∀ i, Fintype (Y i)]
variable [hXd : ∀ i, DecidableEq (X i)] [hYd : ∀ i, DecidableEq (Y i)]

/-- `Hist` is finite. -/
instance histFintype : ∀ k, Fintype (Hist X Y k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 =>
    have := histFintype k
    inferInstanceAs (Fintype ((Hist X Y k × X k) × Y k))

/-- `Hist` has decidable equality. -/
instance histDecEq : ∀ k, DecidableEq (Hist X Y k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 =>
    have := histDecEq k
    inferInstanceAs (DecidableEq ((Hist X Y k × X k) × Y k))

/-- Unfold one turn of the history. -/
abbrev histSucc (k : ℕ) : Hist X Y (k + 1) = ((Hist X Y k × X k) × Y k) := rfl

/-- The causal partial-trace constraint between consecutive prefixes. -/
def Causal (k : ℕ) (Qk : Matrix (Hist X Y k) (Hist X Y k) ℂ)
    (Qk1 : Matrix (Hist X Y (k + 1)) (Hist X Y (k + 1)) ℂ) : Prop :=
  traceRight (Qk1 : Matrix ((Hist X Y k × X k) × Y k) ((Hist X Y k × X k) × Y k) ℂ) =
    Qk ⊗ₖ (1 : Matrix (X k) (X k) ℂ)

/-- A `r`-turn strategy operator together with its prefixes. -/
structure IsStrategy (r : ℕ) (Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ) : Prop where
  zero : Q 0 = 1
  posSemidef : ∀ k ≤ r, (Q k).PosSemidef
  causal : ∀ k < r, Causal k (Q k) (Q (k + 1))

/-- **Trace normalization**: `trace (Q k) = ∏_{i < k} card (X i)`. -/
theorem IsStrategy.trace_eq {r : ℕ} {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ}
    (h : IsStrategy r Q) : ∀ k ≤ r, trace (Q k) = ∏ i ∈ Finset.range k, (Fintype.card (X i) : ℂ)
  | 0, _ => by
    rw [h.zero, trace_one, Finset.prod_range_zero]
    show ((Fintype.card Unit : ℕ) : ℂ) = 1
    simp
  | k + 1, hk => by
    have hc := h.causal k (by omega)
    have ih := IsStrategy.trace_eq h k (by omega)
    have e : trace (Q (k + 1)) =
        trace (traceRight (Q (k + 1) :
          Matrix ((Hist X Y k × X k) × Y k) ((Hist X Y k × X k) × Y k) ℂ)) :=
      (trace_traceRight _).symm
    rw [e, hc, trace_kronecker, ih, trace_one, Finset.prod_range_succ]

theorem kronecker_one_injective {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {A B : Matrix β β ℂ} (h : A ⊗ₖ (1 : Matrix α α ℂ) = B ⊗ₖ (1 : Matrix α α ℂ)) : A = B := by
  ext i j
  obtain ⟨a⟩ := ‹Nonempty α›
  have := congrFun (congrFun h (i, a)) (j, a)
  simpa [kronecker_apply] using this

/-- **Prefix uniqueness**: the prefixes of a strategy are determined by its final operator
(all input registers nonempty). -/
theorem IsStrategy.prefix_unique [∀ i, Nonempty (X i)] {r : ℕ}
    {Q Q' : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (h : IsStrategy r Q) (h' : IsStrategy r Q')
    (hr : Q r = Q' r) : ∀ k ≤ r, Q k = Q' k := by
  intro k hk
  induction hk' : r - k generalizing k with
  | zero => have : k = r := by omega
            subst this; exact hr
  | succ d ih =>
    have hk1 : k + 1 ≤ r := by omega
    have e := ih (k + 1) hk1 (by omega)
    have c := h.causal k (by omega)
    have c' := h'.causal k (by omega)
    unfold Causal at c c'
    rw [e] at c
    exact kronecker_one_injective (c.symm.trans c')

/-! ## One turn -/

/-- The one-turn history `(Unit × X 0) × Y 0` is `X 0 × Y 0`. -/
def histOneEquiv : Hist X Y 1 ≃ X 0 × Y 0 :=
  ((Equiv.punitProd (X 0)).prodCongr (Equiv.refl (Y 0)))

/-- A one-turn family from a matrix on `X 0 × Y 0`. -/
def oneTurn (J : Matrix (X 0 × Y 0) (X 0 × Y 0) ℂ) : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ
  | 0 => 1
  | 1 => Matrix.reindex histOneEquiv.symm histOneEquiv.symm J
  | _ + 2 => 0

omit hX in
theorem isStrategy_one_iff (J : Matrix (X 0 × Y 0) (X 0 × Y 0) ℂ) :
    IsStrategy 1 (oneTurn J) ↔ J.PosSemidef ∧ traceRight J = 1 := by
  have hpsd : (oneTurn (X := X) (Y := Y) J 1).PosSemidef ↔ J.PosSemidef := by
    change (Matrix.reindex histOneEquiv.symm histOneEquiv.symm J).PosSemidef ↔ _
    rw [reindex_apply]; exact posSemidef_submatrix_equiv _
  have hcaus : Causal 0 (oneTurn (X := X) (Y := Y) J 0) (oneTurn J 1) ↔ traceRight J = 1 := by
    unfold Causal
    change traceRight (Matrix.reindex (((Equiv.punitProd (X 0)).symm).prodCongr
        (Equiv.refl (Y 0))) (((Equiv.punitProd (X 0)).symm).prodCongr (Equiv.refl (Y 0))) J) =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ (1 : Matrix (X 0) (X 0) ℂ) ↔ _
    rw [one_kronecker_one, traceRight_reindex_left]
    constructor
    · intro h
      ext a b
      have := congrFun (congrFun h ((), a)) ((), b)
      simpa [one_apply] using this
    · intro h
      rw [h]
      ext ⟨u, a⟩ ⟨v, b⟩
      simp [one_apply]
  constructor
  · intro h
    exact ⟨hpsd.mp (h.posSemidef 1 le_rfl), hcaus.mp (h.causal 0 (by omega))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨rfl, fun k hk => ?_, fun k hk => ?_⟩
    · interval_cases k
      · exact PosSemidef.one
      · exact hpsd.mpr h1
    · interval_cases k
      exact hcaus.mpr h2

/-- **One-turn strategies are Choi matrices of channels.** -/
theorem isStrategy_one_iff_choi (Φ : MatMap (X 0) (Y 0)) :
    IsStrategy 1 (oneTurn (X := X) (Y := Y) (choi Φ)) ↔ IsChannel Φ := by
  rw [isStrategy_one_iff, ← isCP_iff_choi_posSemidef, ← isTP_iff_traceRight_choi]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **State preparation**: with a one-dimensional input, one-turn strategies are exactly
density operators on the output. -/
theorem isStrategy_one_prep_iff (hX0 : X 0 = Unit) (J : Matrix (X 0 × Y 0) (X 0 × Y 0) ℂ) :
    IsStrategy 1 (oneTurn J) ↔ J.PosSemidef ∧ trace J = 1 := by
  rw [isStrategy_one_iff]
  have : Unique (X 0) := hX0 ▸ inferInstanceAs (Unique Unit)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [← trace_traceRight, h2, trace_one, Fintype.card_unique, Nat.cast_one]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext a b
    rw [Subsingleton.elim a default, Subsingleton.elim b default, one_apply_eq]
    rw [← trace_traceRight] at h2
    simpa [trace, Fintype.sum_unique] using h2

end ShiQIP
