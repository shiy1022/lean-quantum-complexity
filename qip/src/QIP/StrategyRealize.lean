/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.StrategyRealization
import Quantum.Completion

/-!
# Q19 (reverse direction) — realization of causal strategy operators

**`isStrategy_iff_realized`**: for nonempty registers, a family `Q` satisfies the causal
constraints `IsStrategy r Q` **iff** it is `stratOp S` for an operational strategy `S`. The
realizing strategy has memory `M k = Hist X Y k` (`exists_opStrategy_of_isStrategy`), so its
memory dimension is bounded by `∏_{i<k} card (X i) · card (Y i)`.

Construction, turn by turn, keeping the memory state **pure**:

* `memState k = |ψ_k⟩⟨ψ_k|` for the canonical purification `ψ_k = purify (Q k)`;
* `ψ_k ⊗ Ω_{X k}` (re-ordered to `(Hist k × X k) × (X k × Hist k)`) purifies `Q k ⊗ 1`
  (`isPurification_linkVec`), and `ψ_{k+1}` re-associated to `(Hist k × X k) × (Y k × Hist (k+1))`
  purifies `Tr_{Y k} Q (k+1) = Q k ⊗ 1` (causality);
* the padded equal-marginal theorem gives a contraction `B` with `vecToMat ψ' = vecToMat u * B`
  (`exists_contraction_relating`). Then `K = Bᵀ` maps `u` to `ψ'` while preserving its norm, and
  the completed channel `krausMap (completeKraus K f₀)` does the same on `|u⟩⟨u|`
  (`liftR_completeKraus_pureState`). This is the turn (`exists_turn`).

Singular (rank-deficient) prefixes need no special treatment: no inverse is ever taken.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

/-- Histories over nonempty registers are nonempty. -/
instance histNonempty [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)] : ∀ k, Nonempty (Hist X Y k)
  | 0 => inferInstanceAs (Nonempty Unit)
  | k + 1 =>
    have := histNonempty k
    inferInstanceAs (Nonempty ((Hist X Y k × X k) × Y k))

/-! ## Relating two factors by a contraction -/

theorem exists_contraction_relating {n E F : Type} [Fintype n] [DecidableEq n] [Fintype E]
    [DecidableEq E] [Fintype F] [DecidableEq F] {M : Matrix n E ℂ} {N : Matrix n F ℂ}
    (h : M * Mᴴ = N * Nᴴ) : ∃ B : Matrix E F ℂ, N = M * B ∧ B * Bᴴ ≤ 1 := by
  obtain ⟨U, hU, hpad⟩ := exists_unitary_padded h
  refine ⟨U.toBlocks₁₂, ?_, (unitary_block12_contractions hU).1⟩
  ext i f
  have := congrFun (congrFun hpad i) (Sum.inr f)
  rw [fromCols_apply_inr, mul_apply, Fintype.sum_sum_type] at this
  rw [this, mul_apply]
  simp [Matrix.zero_apply, toBlocks₁₂]

theorem transpose_contraction {E F : Type} [Fintype E] [DecidableEq E] [Fintype F]
    [DecidableEq F] {B : Matrix E F ℂ} (hB : B * Bᴴ ≤ 1) : (Bᵀ)ᴴ * Bᵀ ≤ 1 := by
  have e : (Bᵀ)ᴴ * Bᵀ = (B * Bᴴ)ᵀ := by
    ext a b; simp [mul_apply, conjTranspose_apply, mul_comm]
  rw [e, Matrix.le_iff, ← transpose_one, ← transpose_sub]
  exact (Matrix.le_iff.mp hB).transpose

/-! ## One turn -/

/-- `ψ ⊗ Ω`, re-ordered to `(H × X) × (X × M)`. -/
def linkVec {H Xx Mm : Type} [DecidableEq Xx] (ψ : H × Mm → ℂ) : (H × Xx) × (Xx × Mm) → ℂ :=
  (fun p : (H × Mm) × (Xx × Xx) => ψ p.1 * omegaVec Xx p.2) ∘ (linkEquiv H Mm Xx).symm

theorem pureState_linkVec {H Xx Mm : Type} [Fintype H] [Fintype Xx] [DecidableEq Xx] [Fintype Mm]
    (ψ : H × Mm → ℂ) :
    Matrix.reindex (linkEquiv H Mm Xx) (linkEquiv H Mm Xx)
      (pureState ψ ⊗ₖ vecMulVec (omegaVec Xx) (star (omegaVec Xx))) = pureState (linkVec ψ) := by
  rw [show vecMulVec (omegaVec Xx) (star (omegaVec Xx)) = pureState (omegaVec Xx) from rfl,
    kronecker_pureState, reindex_pureState]
  rfl

theorem isPurification_linkVec {H Xx Mm : Type} [Fintype H] [Fintype Xx] [DecidableEq Xx]
    [Fintype Mm] {ψ : H × Mm → ℂ} {ρ : Matrix H H ℂ} (hψ : IsPurification ψ ρ) :
    IsPurification (linkVec (Xx := Xx) ψ) (ρ ⊗ₖ (1 : Matrix Xx Xx ℂ)) := by
  rw [IsPurification, ← pureState_linkVec, traceRight_link]
  rw [IsPurification] at hψ
  rw [hψ]

theorem star_dotProduct_eq_trace {α : Type} [Fintype α] (v : α → ℂ) : star v ⬝ᵥ v = trace (pureState v) := by
  rw [pureState, trace_rankOne]

/-- **One turn of the realization.** -/
theorem exists_turn [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)] {r : ℕ}
    {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (hQ : IsStrategy r Q) (k : ℕ) (hk : k < r) :
    ∃ Φ : MatMap (X k × Hist X Y k) (Y k × Hist X Y (k + 1)), IsChannel Φ ∧
      linkStep Φ (pureState (purify (Q k))) =
        pureState (reassocVec (A := Hist X Y k × X k) (B := Y k) (E := Hist X Y (k + 1)) (purify (Q (k + 1)))) := by
  have hk0 := hQ.posSemidef k (by omega)
  have hk1 := hQ.posSemidef (k + 1) (by omega)
  set u := linkVec (Xx := X k) (purify (Q k))
  set φ' := reassocVec (A := Hist X Y k × X k) (B := Y k) (E := Hist X Y (k + 1)) (purify (Q (k + 1)))
  have hu : IsPurification u (Q k ⊗ₖ (1 : Matrix (X k) (X k) ℂ)) :=
    isPurification_linkVec (purify_isPurification hk0)
  have hφ : IsPurification φ' (Q k ⊗ₖ (1 : Matrix (X k) (X k) ℂ)) := by
    have := (purify_isPurification hk1).reassoc (A := Hist X Y k × X k) (B := Y k)
      (E := Hist X Y (k + 1))
    have hc := hQ.causal k hk
    unfold Causal at hc
    rwa [hc] at this
  rw [isPurification_iff] at hu hφ
  obtain ⟨B, hB, hBc⟩ := exists_contraction_relating (hu.trans hφ.symm)
  set K := Bᵀ
  have hK : Kᴴ * K ≤ 1 := transpose_contraction hBc
  have hKu : ((1 : Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ) ⊗ₖ K) *ᵥ u = φ' := by
    have := matToVec_mul u B
    rw [← hB] at this
    exact this.symm
  have hnorm : star (((1 : Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ) ⊗ₖ K) *ᵥ u) ⬝ᵥ
      (((1 : Matrix (Hist X Y k × X k) (Hist X Y k × X k) ℂ) ⊗ₖ K) *ᵥ u) = star u ⬝ᵥ u := by
    have t1 : trace (pureState φ') = trace (Q k ⊗ₖ (1 : Matrix (X k) (X k) ℂ)) := by
      rw [← trace_traceRight, traceRight_pureState, hφ]
    have t2 : trace (pureState u) = trace (Q k ⊗ₖ (1 : Matrix (X k) (X k) ℂ)) := by
      rw [← trace_traceRight, traceRight_pureState, hu]
    rw [hKu, star_dotProduct_eq_trace, star_dotProduct_eq_trace, t1, t2]
  obtain ⟨f₀⟩ := (inferInstance : Nonempty (Y k × Hist X Y (k + 1)))
  refine ⟨krausMap (completeKraus K f₀), isChannel_completeKraus hK f₀, ?_⟩
  rw [linkStep, pureState_linkVec, liftR_completeKraus_pureState hK f₀ hnorm, hKu]

/-! ## The realizing strategy -/

variable [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)] {r : ℕ}

/-- The realizing operational strategy, with memory `Hist X Y k`. -/
noncomputable def realize {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (hQ : IsStrategy r Q) :
    OpStrategy X Y r where
  M k := Hist X Y k
  init := 1
  init_density := by
    have : Unique (Hist X Y 0) := inferInstanceAs (Unique Unit)
    rw [isDensity_unique_iff]
  act k := if h : k < r then Classical.choose (exists_turn hQ k h) else 0
  act_channel k hk := by
    simp only [dif_pos hk]
    exact (Classical.choose_spec (exists_turn hQ k hk)).1

theorem purify_one_unit : purify (1 : Matrix Unit Unit ℂ) = fun _ => 1 := by
  have : psdSqrt (1 : Matrix Unit Unit ℂ) = 1 :=
    psdSqrt_unique PosSemidef.one (Matrix.one_mul 1)
  funext p
  simp [purify, matToVec, this]

theorem memState_realize {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ} (hQ : IsStrategy r Q) :
    ∀ k ≤ r, memState (realize hQ) k = pureState (purify (Q k))
  | 0, _ => by
    rw [hQ.zero]
    change Matrix.reindex (Equiv.punitProd Unit).symm (Equiv.punitProd Unit).symm
      (1 : Matrix Unit Unit ℂ) = pureState (purify (1 : Matrix Unit Unit ℂ))
    rw [purify_one_unit]
    ext a b
    simp [pureState, vecMulVec_apply]
  | k + 1, hk => by
    have ih := memState_realize hQ k (by omega)
    have hk' : k < r := by omega
    have hspec := (Classical.choose_spec (exists_turn hQ k hk')).2
    change Matrix.reindex _ _ (linkStep ((realize hQ).act k) (memState (realize hQ) k)) = _
    rw [ih]
    have hact : (realize hQ).act k = Classical.choose (exists_turn hQ k hk') := by
      simp [realize, dif_pos hk']
    rw [hact]
    refine (congrArg (Matrix.reindex
      (Equiv.prodAssoc (Hist X Y k × X k) (Y k) (Hist X Y (k + 1))).symm
      (Equiv.prodAssoc (Hist X Y k × X k) (Y k) (Hist X Y (k + 1))).symm) hspec).trans ?_
    rw [reindex_pureState]
    rfl

/-- **Realization**: every causal family is induced by an operational strategy with memory
`Hist X Y k`. -/
theorem exists_opStrategy_of_isStrategy {Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ}
    (hQ : IsStrategy r Q) :
    ∃ S : OpStrategy X Y r, (∀ k, S.M k = Hist X Y k) ∧ ∀ k ≤ r, stratOp S k = Q k :=
  ⟨realize hQ, fun _ => rfl, fun k hk => by
    rw [stratOp, memState_realize hQ k hk]
    exact purify_isPurification (hQ.posSemidef k hk)⟩

/-- **Strategy representation, both directions.** -/
theorem isStrategy_iff_realized (Q : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ) :
    IsStrategy r Q ↔ ∃ S : OpStrategy X Y r, ∀ k ≤ r, stratOp S k = Q k := by
  constructor
  · intro hQ
    obtain ⟨S, -, hS⟩ := exists_opStrategy_of_isStrategy hQ
    exact ⟨S, hS⟩
  · rintro ⟨S, hS⟩
    have h := opStrategy_isStrategy S
    refine ⟨?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hS 0 (Nat.zero_le _)]; exact h.zero
    · rw [← hS k hk]; exact h.posSemidef k hk
    · rw [← hS k (by omega), ← hS (k + 1) hk]; exact h.causal k hk

end ShiQIP
