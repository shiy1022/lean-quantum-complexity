/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.PureRun
import QIP.Circuit.Relabel

/-!
# Prefixes of verifier descriptions

A description `D` **extends** `d` (`PrefixData d D`) when the following hold.

* The wires of `d` embed into those of `D` (`ε`); the remaining wires of `D` start at `|0⟩`.
* For every message `j < m = d.numMsgs`, the message register `j` of `D` is the image of the
  message register `j` of `d`.
* The blocks `j < m` of `D` are those of `d`, tensored with the identity. Block `m` is block `m`
  of `d` followed by a fixed unitary `G`.

`D` may have further messages and blocks after `m`.

For an isometric prover `T` of `D`, its first `m` turns, transported along the register
bijections `τ`, give an isometric prover `restrict T` of `d`. The pure global states agree:
`pureRun_prefix` (`j < m`) and `pureRun_prefix_last` (`j = m`, with `G`). The state of `D` is the
state of `d` with the new wires at `|0⟩` (`embV`).
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-- The data of a prefix. -/
structure PrefixData (d D : Desc) where
  ε : Fin d.totalWires ↪ Fin D.totalWires
  le_msgs : d.numMsgs ≤ D.numMsgs
  reg : ∀ j < d.numMsgs, ∀ x, inReg D j (ε x) ↔ inReg d j x
  reg_range : ∀ j < d.numMsgs, ∀ v, inReg D j v → v ∈ Set.range ε
  block : ∀ j < d.numMsgs, blockMat D j =
    (blockMat d j ⊗ₖ (1 : Matrix (Outside ε → Bool) (Outside ε → Bool) ℂ)).submatrix
      (embSplit ε) (embSplit ε)
  G : Matrix (Qubits D.totalWires) (Qubits D.totalWires) ℂ
  block_last : blockMat D d.numMsgs = G *
    (blockMat d d.numMsgs ⊗ₖ (1 : Matrix (Outside ε → Bool) (Outside ε → Bool) ℂ)).submatrix
      (embSplit ε) (embSplit ε)

namespace PrefixData

variable {d D : Desc} (Pf : PrefixData d D)

/-- Register positions of `d` inside `D`. -/
def regMapP (j : ℕ) (hj : j < d.numMsgs) : {x // inReg d j x} → {v // inReg D j v} :=
  fun x => ⟨Pf.ε x.1, (Pf.reg j hj x.1).mpr x.2⟩

theorem regMapP_bijective (j : ℕ) (hj : j < d.numMsgs) : Function.Bijective (Pf.regMapP j hj) := by
  constructor
  · intro x y h
    exact Subtype.ext (Pf.ε.injective (congrArg Subtype.val h))
  · rintro ⟨v, hv⟩
    obtain ⟨x, rfl⟩ := Pf.reg_range j hj v hv
    exact ⟨⟨x, (Pf.reg j hj x).mp hv⟩, rfl⟩

/-- **The register bijection** `Reg D j ≃ Reg d j` for `j < m`. -/
noncomputable def τ (j : ℕ) (hj : j < d.numMsgs) : Reg D j ≃ Reg d j :=
  Equiv.arrowCongr (Equiv.ofBijective _ (Pf.regMapP_bijective j hj)).symm (Equiv.refl Bool)

theorem τ_apply (j : ℕ) (hj : j < d.numMsgs) (r : Reg D j) (x : {x // inReg d j x}) :
    Pf.τ j hj r x = r (Pf.regMapP j hj x) := by
  simp [τ, Equiv.arrowCongr_apply]

/-- Embed a global vector of `d`, with the new wires at `|0⟩`. -/
noncomputable def embV {M : Type} (v : Qubits d.totalWires × M → ℂ) :
    Qubits D.totalWires × M → ℂ :=
  fun p => if (embSplit Pf.ε p.1).2 = (fun _ => false) then v ((embSplit Pf.ε p.1).1, p.2) else 0

/-- **The restriction of an isometric prover of `D` to `d`.** -/
@[reducible] noncomputable def restrict (T : IsoStrategy (Reg D) (Reg D) D.numMsgs) :
    IsoStrategy (Reg d) (Reg d) d.numMsgs where
  M := T.M
  init := T.init
  init_density := T.init_density
  V k := if h : k < d.numMsgs then
      (T.V k).submatrix (Prod.map (Pf.τ k h).symm id) (Prod.map (Pf.τ k h).symm id) else 0
  V_iso k hk := by
    rw [dif_pos hk, conjTranspose_submatrix,
      show Prod.map (Pf.τ k hk).symm (id : T.M (k + 1) → T.M (k + 1)) =
        ((Pf.τ k hk).symm.prodCongr (Equiv.refl (T.M (k + 1))) : _ → _) from rfl,
      submatrix_mul_equiv, T.V_iso k (lt_of_lt_of_le hk Pf.le_msgs)]
    exact submatrix_one_equiv ((Pf.τ k hk).symm.prodCongr (Equiv.refl _))

theorem restrict_V {T : IsoStrategy (Reg D) (Reg D) D.numMsgs} {k : ℕ} (hk : k < d.numMsgs)
    (a b : Reg D k) (μ : T.M (k + 1)) (ν : T.M k) :
    T.V k (a, μ) (b, ν) = (Pf.restrict T).V k (Pf.τ k hk a, μ) (Pf.τ k hk b, ν) := by
  simp [restrict, dif_pos hk]

/-! ## Register replacement -/

/-- Replace register `j` of `w` by `x`. -/
def regSet (e : Desc) (j : ℕ) (w : Qubits e.totalWires) (x : Reg e j) : Qubits e.totalWires :=
  (wireSplitE e j).symm ((wireSplitE e j w).1, x)

theorem regSet_apply (e : Desc) (j : ℕ) (w : Qubits e.totalWires) (x : Reg e j)
    (v : Fin e.totalWires) :
    regSet e j w x v = if h : inReg e j v then x ⟨v, h⟩ else w v := rfl

theorem turnVec_apply {e : Desc} (T : IsoStrategy (Reg e) (Reg e) e.numMsgs) (j : ℕ)
    (v : Qubits e.totalWires × T.M j → ℂ) (w : Qubits e.totalWires) (μ : T.M (j + 1)) :
    turnVec T j v (w, μ) = ∑ x : Reg e j, ∑ ν : T.M j,
      T.V j ((wireSplitE e j w).2, μ) (x, ν) * v (regSet e j w x, ν) := by
  simp only [turnVec, Function.comp_apply, mulVec, dotProduct, Fintype.sum_prod_type,
    kroneckerMap_apply, one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ((turnSplit e j (T.M (j + 1))) (w, μ)).1]
  · simp only [if_true]
    rfl
  · intro b _ hb
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => if_neg (Ne.symm hb)
  · simp

theorem embSplit_regSet_snd {j : ℕ} (hj : j < d.numMsgs) (w : Qubits D.totalWires) (x : Reg D j) :
    (embSplit Pf.ε (regSet D j w x)).2 = (embSplit Pf.ε w).2 := by
  funext r
  simp only [embSplit_snd, regSet_apply]
  rw [dif_neg]
  · intro h
    obtain ⟨y, hy⟩ := Pf.reg_range j hj r.1 h
    exact r.2 ⟨y, hy⟩

theorem embSplit_regSet_fst {j : ℕ} (hj : j < d.numMsgs) (w : Qubits D.totalWires) (x : Reg D j) :
    (embSplit Pf.ε (regSet D j w x)).1 = regSet d j (embSplit Pf.ε w).1 (Pf.τ j hj x) := by
  funext y
  simp only [embSplit_fst, regSet_apply]
  by_cases h : inReg d j y
  · rw [dif_pos ((Pf.reg j hj y).mpr h), dif_pos h, τ_apply]; rfl
  · rw [dif_neg (fun h' => h ((Pf.reg j hj y).mp h')), dif_neg h]

theorem τ_reg {j : ℕ} (hj : j < d.numMsgs) (w : Qubits D.totalWires) :
    Pf.τ j hj (wireSplitE D j w).2 = (wireSplitE d j (embSplit Pf.ε w).1).2 := by
  funext x; rw [τ_apply]; rfl

/-- **Prover turns commute with the embedding.** -/
theorem turnVec_embV (T : IsoStrategy (Reg D) (Reg D) D.numMsgs) {j : ℕ} (hj : j < d.numMsgs)
    (v : Qubits d.totalWires × T.M j → ℂ) :
    turnVec T j (Pf.embV v) = Pf.embV (turnVec (Pf.restrict T) j v) := by
  funext ⟨w, μ⟩
  rw [turnVec_apply]
  simp only [embV]
  rw [turnVec_apply]
  simp only [embSplit_regSet_snd Pf hj, embSplit_regSet_fst Pf hj, Pf.restrict_V hj,
    τ_reg Pf hj]
  split_ifs with h
  · rw [← (Pf.τ j hj).sum_comp]
  · simp

/-- **Embedded blocks act on embedded vectors.** -/
theorem mulVec_embV {M : Type} [Fintype M] [DecidableEq M]
    (B : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) (v : Qubits d.totalWires × M → ℂ) :
    (((B ⊗ₖ (1 : Matrix (Outside Pf.ε → Bool) (Outside Pf.ε → Bool) ℂ)).submatrix (embSplit Pf.ε)
        (embSplit Pf.ε)) ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ Pf.embV v =
      Pf.embV ((B ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ v) := by
  funext ⟨w, μ⟩
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, submatrix_apply,
    one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, embV]
  rw [← (embSplit Pf.ε).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  split_ifs with h
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp [h]
    · intro z _ hz
      simp [h, Ne.symm hz, hz]
    · simp
  · refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : (embSplit Pf.ε w).2 = z
    · subst hz; simp [h]
    · simp [hz]

theorem zero_embV {M : Type} (init : M → ℂ) :
    (fun p : Qubits D.totalWires × M => zeroVec D.totalWires p.1 * init p.2) =
      Pf.embV fun p => zeroVec d.totalWires p.1 * init p.2 := by
  funext ⟨w, μ⟩
  simp only [embV, zeroVec]
  have key : w = Qubits.zero _ ↔ (embSplit Pf.ε w).1 = Qubits.zero _ ∧
      (embSplit Pf.ε w).2 = fun _ => false := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      apply (embSplit Pf.ε).injective
      rw [Prod.ext_iff]; exact ⟨h1, h2⟩
  by_cases h : w = Qubits.zero _
  · rw [if_pos h, if_pos (key.mp h).2, if_pos (key.mp h).1]
  · rw [if_neg h, zero_mul]
    split_ifs with h2 h1
    · exact absurd (key.mpr ⟨h1, h2⟩) h
    · simp
    · rfl

/-- **The pure run of `D` is the embedded pure run of `d`, before block `m`.** -/
theorem pureRun_prefix (T : IsoStrategy (Reg D) (Reg D) D.numMsgs) :
    ∀ j < d.numMsgs, pureRun T j = Pf.embV (pureRun (Pf.restrict T) j)
  | 0, h => by
    rw [pureRun, pureRun, Pf.block 0 h, zero_embV, mulVec_embV]
  | j + 1, h => by
    rw [pureRun, pureRun, pureRun_prefix T j (by omega), turnVec_embV Pf T (by omega),
      Pf.block (j + 1) h, mulVec_embV]

/-- **At block `m`, the fixed unitary `G` follows.** -/
theorem pureRun_prefix_last (T : IsoStrategy (Reg D) (Reg D) D.numMsgs) :
    pureRun T d.numMsgs = (Pf.G ⊗ₖ (1 : Matrix (T.M d.numMsgs) (T.M d.numMsgs) ℂ)) *ᵥ
      Pf.embV (pureRun (Pf.restrict T) d.numMsgs) := by
  have e : ∀ k, k = d.numMsgs → pureRun T k = (Pf.G ⊗ₖ (1 : Matrix (T.M k) (T.M k) ℂ)) *ᵥ
      Pf.embV (pureRun (Pf.restrict T) k) := by
    intro k hk
    have hb := Pf.block_last
    rw [← hk] at hb
    cases k with
    | zero =>
      rw [pureRun, pureRun, hb, zero_embV, ← one_mul (1 : Matrix (T.M 0) (T.M 0) ℂ),
        mul_kronecker_mul, ← mulVec_mulVec, mulVec_embV, one_mul]
    | succ k =>
      rw [pureRun, pureRun, pureRun_prefix Pf T k (by omega), turnVec_embV Pf T (by omega), hb,
        ← one_mul (1 : Matrix (T.M (k + 1)) (T.M (k + 1)) ℂ), mul_kronecker_mul, ← mulVec_mulVec,
        mulVec_embV, one_mul]
  exact e _ rfl

end PrefixData

end ShiQIP
