/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Prefix
import QIP.SDP.Product

/-!
# Reduced states on selected wires

For an embedding `f : Fin k ↪ Fin W` of wire positions and a global state `ρ` on the wires and a
memory, `reduceTo f ρ` is the reduced state on the wires `f 0, …, f (k-1)`.

* `trace_mul_local`: local observables only see the reduced state;
* **`reduceTo_proverStep`**: a prover turn does not change the reduced state on wires outside
  its message register.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {W k : ℕ} {M : Type} [Fintype M] [DecidableEq M]

/-- The reduced state on the wires in the image of `f`. -/
noncomputable def reduceTo (f : Fin k ↪ Fin W) (ρ : Matrix (Qubits W × M) (Qubits W × M) ℂ) :
    Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun a a' => ∑ z : Outside f → Bool, ∑ μ : M,
    ρ ((embSplit f).symm (a, z), μ) ((embSplit f).symm (a', z), μ)

/-- The operator `X` on the wires of `f`, the identity elsewhere and on the memory. -/
noncomputable def localOp (f : Fin k ↪ Fin W) (M : Type) [DecidableEq M]
    (X : Matrix (Qubits k) (Qubits k) ℂ) : Matrix (Qubits W × M) (Qubits W × M) ℂ :=
  ((X ⊗ₖ (1 : Matrix (Outside f → Bool) (Outside f → Bool) ℂ)).submatrix (embSplit f)
    (embSplit f)) ⊗ₖ (1 : Matrix M M ℂ)

/-- Split the wires at `f`, keeping the memory with the other wires. -/
noncomputable def splitMem (f : Fin k ↪ Fin W) (M : Type) :
    Qubits W × M ≃ Qubits k × ((Outside f → Bool) × M) :=
  ((embSplit f).prodCongr (Equiv.refl M)).trans (Equiv.prodAssoc _ _ _)

omit [Fintype M] in
theorem localOp_eq (f : Fin k ↪ Fin W) (X : Matrix (Qubits k) (Qubits k) ℂ) :
    localOp f M X = (X ⊗ₖ (1 : Matrix ((Outside f → Bool) × M) ((Outside f → Bool) × M) ℂ)).submatrix
      (splitMem f M) (splitMem f M) := by
  ext ⟨w, μ⟩ ⟨w', μ'⟩
  simp only [localOp, splitMem, kroneckerMap_apply, submatrix_apply, one_apply, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.coe_refl, id, Equiv.prodAssoc_apply, Prod.mk.injEq]
  by_cases h1 : (embSplit f w).2 = (embSplit f w').2 <;> by_cases h2 : μ = μ' <;> simp [h1, h2]

omit [DecidableEq M] in
theorem reduceTo_eq (f : Fin k ↪ Fin W) (ρ : Matrix (Qubits W × M) (Qubits W × M) ℂ) :
    reduceTo f ρ = traceRight (ρ.submatrix (splitMem f M).symm (splitMem f M).symm) := by
  ext a a'
  simp only [reduceTo, of_apply, traceRight_apply, submatrix_apply, Fintype.sum_prod_type]
  rfl

/-- **Local observables only see the reduced state.** -/
theorem trace_localOp_mul (f : Fin k ↪ Fin W) (X : Matrix (Qubits k) (Qubits k) ℂ)
    (ρ : Matrix (Qubits W × M) (Qubits W × M) ℂ) :
    trace (localOp f M X * ρ) = trace (X * reduceTo f ρ) := by
  rw [localOp_eq, reduceTo_eq, trace_mul_traceRight,
    ← trace_submatrix_equiv _ (splitMem f M), ← submatrix_mul_equiv (e₂ := splitMem f M)]
  simp [submatrix_submatrix]

theorem reduceTo_ext {M' : Type} [Fintype M'] [DecidableEq M'] {f : Fin k ↪ Fin W}
    {ρ : Matrix (Qubits W × M) (Qubits W × M) ℂ} {σ : Matrix (Qubits W × M') (Qubits W × M') ℂ}
    (h : ∀ X, trace (localOp f M X * ρ) = trace (localOp f M' X * σ)) :
    reduceTo f ρ = reduceTo f σ := by
  ext a a'
  have := h (Matrix.single a' a 1)
  rw [trace_localOp_mul, trace_localOp_mul, trace_single_mul, trace_single_mul] at this
  simpa using this

/-! ## Prover turns do not change reduced states outside their register -/

/-- The operator `X` on the wires of `f`, as an operator on the wires outside register `j`. -/
noncomputable def restOp (d : Desc) (j : ℕ) {k : ℕ} (f : Fin k ↪ Fin d.totalWires)
    (X : Matrix (Qubits k) (Qubits k) ℂ) : Matrix (Rest d j) (Rest d j) ℂ :=
  Matrix.of fun r r' =>
    ((X ⊗ₖ (1 : Matrix (Outside f → Bool) (Outside f → Bool) ℂ)).submatrix (embSplit f)
      (embSplit f)) ((wireSplitE d j).symm (r, fun _ => false))
        ((wireSplitE d j).symm (r', fun _ => false))

theorem localOp_turn (d : Desc) (j : ℕ) {k : ℕ} (f : Fin k ↪ Fin d.totalWires)
    (hf : ∀ i, ¬ inReg d j (f i)) (Mem : Type) [DecidableEq Mem]
    (X : Matrix (Qubits k) (Qubits k) ℂ) :
    localOp f Mem X = (restOp d j f X ⊗ₖ
      (1 : Matrix (Reg d j × Mem) (Reg d j × Mem) ℂ)).submatrix (turnSplit d j Mem)
        (turnSplit d j Mem) := by
  ext ⟨w, μ⟩ ⟨w', μ'⟩
  simp only [localOp, restOp, kroneckerMap_apply, submatrix_apply, of_apply, one_apply]
  change _ = X (embSplit f ((wireSplitE d j).symm ((wireSplitE d j w).1, fun _ => false))).1
      (embSplit f ((wireSplitE d j).symm ((wireSplitE d j w').1, fun _ => false))).1 *
    (if (embSplit f ((wireSplitE d j).symm ((wireSplitE d j w).1, fun _ => false))).2 =
      (embSplit f ((wireSplitE d j).symm ((wireSplitE d j w').1, fun _ => false))).2 then 1 else 0) *
    (if ((wireSplitE d j w).2, μ) = ((wireSplitE d j w').2, μ') then 1 else 0)
  have hfst : ∀ u : Qubits d.totalWires,
      (embSplit f ((wireSplitE d j).symm ((wireSplitE d j u).1, fun _ => false))).1 =
        (embSplit f u).1 := by
    intro u; funext i
    change (if h : inReg d j (f i) then false else u (f i)) = u (f i)
    rw [dif_neg (hf i)]
  have hreg : (wireSplitE d j w).2 = (wireSplitE d j w').2 ↔
      ∀ v (h : inReg d j v), w v = w' v :=
    ⟨fun h v hv => congrFun h ⟨v, hv⟩, fun h => funext fun r => h r.1 r.2⟩
  have hout : (embSplit f w).2 = (embSplit f w').2 ↔
      ((embSplit f ((wireSplitE d j).symm ((wireSplitE d j w).1, fun _ => false))).2 =
        (embSplit f ((wireSplitE d j).symm ((wireSplitE d j w').1, fun _ => false))).2 ∧
        (wireSplitE d j w).2 = (wireSplitE d j w').2) := by
    rw [hreg]
    constructor
    · intro h
      refine ⟨funext fun o => ?_, fun v hv => ?_⟩
      · change (if h : inReg d j o.1 then false else w o.1) =
          (if h : inReg d j o.1 then false else w' o.1)
        split_ifs
        · rfl
        · exact congrFun h o
      · have : v ∉ Set.range f := fun ⟨i, hi⟩ => hf i (hi ▸ hv)
        exact congrFun h ⟨v, this⟩
    · rintro ⟨h1, h2⟩
      funext o
      by_cases ho : inReg d j o.1
      · exact h2 o.1 ho
      · have := congrFun h1 o
        change (if h : inReg d j o.1 then false else w o.1) =
          (if h : inReg d j o.1 then false else w' o.1) at this
        rwa [dif_neg ho, dif_neg ho] at this
  rw [hfst, hfst]
  by_cases h1 : (embSplit f w).2 = (embSplit f w').2
  · obtain ⟨ha, hb⟩ := hout.mp h1
    rw [if_pos h1, if_pos ha]
    by_cases h2 : μ = μ' <;> simp [h2, hb]
  · rw [if_neg h1]
    by_cases ha : (embSplit f ((wireSplitE d j).symm ((wireSplitE d j w).1, fun _ => false))).2 =
        (embSplit f ((wireSplitE d j).symm ((wireSplitE d j w').1, fun _ => false))).2
    · rw [if_pos ha]
      have hb : ¬ (wireSplitE d j w).2 = (wireSplitE d j w').2 := fun hb => h1 (hout.mpr ⟨ha, hb⟩)
      simp only [Prod.mk.injEq, hb, false_and, if_false, mul_zero]
      simp
    · rw [if_neg ha]; simp

theorem trace_submatrix_mul {m n : Type} [Fintype m] [Fintype n] (A : Matrix n n ℂ) (e : m ≃ n)
    (B : Matrix m m ℂ) : trace (A.submatrix e e * B) = trace (A * B.submatrix e.symm e.symm) := by
  conv_lhs => rw [show B = (B.submatrix e.symm e.symm).submatrix e e by simp [submatrix_submatrix]]
  rw [submatrix_mul_equiv, trace_submatrix_equiv]

/-- **A prover turn leaves the reduced state outside its register unchanged.** -/
theorem reduceTo_proverStep {d : Desc} (P : Prover d) {j : ℕ} (hj : j < d.numMsgs)
    {k : ℕ} (f : Fin k ↪ Fin d.totalWires) (hf : ∀ i, ¬ inReg d j (f i))
    (ρ : Matrix (Qubits d.totalWires × P.M j) (Qubits d.totalWires × P.M j) ℂ) :
    reduceTo f (proverStep P j ρ) = reduceTo f ρ := by
  apply reduceTo_ext
  intro X
  rw [localOp_turn d j f hf, localOp_turn d j f hf, trace_submatrix_mul, trace_submatrix_mul]
  simp only [proverStep, LinearMap.comp_apply, reindexMap_apply, reindex_apply, Equiv.symm_symm,
    submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  rw [← trace_mul_traceRight, ← trace_mul_traceRight, traceRight_liftR (P.act_channel j hj).tp]

end ShiQIP
