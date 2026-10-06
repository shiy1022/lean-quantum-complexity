/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.UnitaryProver
import QIP.Clean

/-!
# Q30 — the generalized prover model

Between blocks `k` and `k + 1` the verifier keeps the wires held during both blocks
(`kept d k`). A **generalized prover** acts at that turn by an arbitrary unitary on *all other
wires* and its memory, and may start from any state whose wires held during block `0` read `0`.
This is the model of Kitaev–Watrous; it lets the cut-state arguments use unitaries on everything
outside the verifier.

* `gsplit`, `gturn`, `GProver`, `gRun`, `gAcc`, `GInit`;
* turns of register-and-memory matrices: `tv`, `tv_apply`, `tv_mul`, `pmat`, `tv_pmat`;
* the simulation: a legal prover `simT` keeps a virtual copy of every wire the verifier does not
  hold, swaps its message register in (`σin`) or out (`σout`) and applies the generalized unitary
  to the copy (`UL`, `tv_UL`, `tv_swap_form`, `turnVec_simT`, `pureRun_simT`);
* **`gAcc_le_value`**: a generalized prover is accepted with probability at most `value d`.
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable (d : Desc)

/-- The verifier keeps wire `w` across turn `k`. -/
def kept (k : ℕ) (w : Fin d.totalWires) : Prop := d.held k w = true ∧ d.held (k + 1) w = true

instance (k : ℕ) : DecidablePred (kept d k) := fun _ => by unfold kept; infer_instance

/-- The kept wires. -/
abbrev KS (k : ℕ) : Type := {w : Fin d.totalWires // kept d k w} → Bool

/-- The wires on the prover's side during turn `k`. -/
abbrev PS (k : ℕ) : Type := {w : Fin d.totalWires // ¬ kept d k w} → Bool

instance (k : ℕ) : Fintype (KS d k) := inferInstance
instance (k : ℕ) : DecidableEq (KS d k) := inferInstance
instance (k : ℕ) : Fintype (PS d k) := inferInstance
instance (k : ℕ) : DecidableEq (PS d k) := inferInstance

/-- Split basis labels and memory at turn `k`. -/
def gsplit (k : ℕ) (N : Type) : Qubits d.totalWires × N ≃ KS d k × (PS d k × N) :=
  ((Equiv.piEquivPiSubtypeProd (kept d k) (fun _ => Bool)).prodCongr (Equiv.refl N)).trans
    (Equiv.prodAssoc _ _ _)

/-- **A generalized prover**: one memory, a unitary on the prover's side at every turn. -/
structure GProver where
  N : Type
  [fin : Fintype N]
  [dec : DecidableEq N]
  U : ∀ k, Matrix (PS d k × N) (PS d k × N) ℂ
  unit : ∀ k, U k ∈ Matrix.unitaryGroup (PS d k × N) ℂ

attribute [instance] GProver.fin GProver.dec

variable {d}

/-- A generalized turn. -/
noncomputable def gturn (G : GProver d) (k : ℕ) (v : Qubits d.totalWires × G.N → ℂ) :
    Qubits d.totalWires × G.N → ℂ :=
  (((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ G.U k) *ᵥ (v ∘ (gsplit d k G.N).symm)) ∘ gsplit d k G.N

/-- **The generalized run**, from an initial state `ξ₀`: the state after block `j`. -/
noncomputable def gRun (G : GProver d) (ξ₀ : Qubits d.totalWires × G.N → ℂ) :
    ℕ → Qubits d.totalWires × G.N → ℂ
  | 0 => (blockMat d 0 ⊗ₖ (1 : Matrix G.N G.N ℂ)) *ᵥ ξ₀
  | j + 1 => (blockMat d (j + 1) ⊗ₖ (1 : Matrix G.N G.N ℂ)) *ᵥ gturn G j (gRun G ξ₀ j)

/-- The acceptance probability of a generalized run. -/
noncomputable def gAcc (G : GProver d) (ξ₀ : Qubits d.totalWires × G.N → ℂ) : ℝ :=
  ∑ y, ∑ ν, if outBit d y then ‖gRun G ξ₀ d.numMsgs (y, ν)‖ ^ 2 else 0

variable (d) in
/-- A legal initial state: a unit vector whose wires held during block `0` read `0`. -/
def GInit {N : Type} [Fintype N] (ξ₀ : Qubits d.totalWires × N → ℂ) : Prop :=
  (∑ y, ∑ ν, ‖ξ₀ (y, ν)‖ ^ 2 = 1) ∧
    ∀ y ν, (∃ w : Fin d.totalWires, d.held 0 w = true ∧ y w = true) → ξ₀ (y, ν) = 0

/-! ## Turns given by a matrix on the register and a constant memory -/

section TV

variable {e : Desc} {Mem : Type} [Fintype Mem] [DecidableEq Mem]

/-- The turn of a register-and-memory matrix `A`. -/
noncomputable def tv (k : ℕ) (A : Matrix (Reg e k × Mem) (Reg e k × Mem) ℂ)
    (v : Qubits e.totalWires × Mem → ℂ) : Qubits e.totalWires × Mem → ℂ :=
  (((1 : Matrix (Rest e k) (Rest e k) ℂ) ⊗ₖ A) *ᵥ (v ∘ (turnSplit e k Mem).symm)) ∘ turnSplit e k Mem

omit [DecidableEq Mem] in
theorem tv_apply (k : ℕ) (A : Matrix (Reg e k × Mem) (Reg e k × Mem) ℂ)
    (v : Qubits e.totalWires × Mem → ℂ) (y : Qubits e.totalWires) (μ' : Mem) :
    tv k A v (y, μ') = ∑ x : Reg e k, ∑ μ : Mem,
      A ((wireSplitE e k y).2, μ') (x, μ) * v (PrefixData.regSet e k y x, μ) := by
  simp only [tv, Function.comp_apply, mulVec, dotProduct, Fintype.sum_prod_type,
    kroneckerMap_apply, one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ((turnSplit e k Mem) (y, μ')).1]
  · simp only [if_true]
    rfl
  · intro b _ hb
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => if_neg (Ne.symm hb)
  · simp

omit [DecidableEq Mem] in
theorem tv_submatrix (k : ℕ) (A : Matrix (Reg e k × Mem) (Reg e k × Mem) ℂ)
    (σ τ : Reg e k × Mem ≃ Reg e k × Mem) (v : Qubits e.totalWires × Mem → ℂ)
    (y : Qubits e.totalWires) (μ' : Mem) :
    tv k (A.submatrix σ τ) v (y, μ') = ∑ x : Reg e k, ∑ μ : Mem,
      A (σ ((wireSplitE e k y).2, μ')) (x, μ) *
        v (PrefixData.regSet e k y (τ.symm (x, μ)).1, (τ.symm (x, μ)).2) := by
  rw [tv_apply]
  simp only [submatrix_apply]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv τ _ _ fun p => by rw [Equiv.symm_apply_apply]

omit [DecidableEq Mem] in
theorem tv_mul (k : ℕ) (A B : Matrix (Reg e k × Mem) (Reg e k × Mem) ℂ)
    (v : Qubits e.totalWires × Mem → ℂ) : tv k (A * B) v = tv k A (tv k B v) := by
  have h : ((((1 : Matrix (Rest e k) (Rest e k) ℂ) ⊗ₖ B) *ᵥ (v ∘ (turnSplit e k Mem).symm)) ∘
      turnSplit e k Mem) ∘ (turnSplit e k Mem).symm =
        ((1 : Matrix (Rest e k) (Rest e k) ℂ) ⊗ₖ B) *ᵥ (v ∘ (turnSplit e k Mem).symm) := by
    funext p; simp
  simp only [tv]
  rw [h, mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul]

/-- The permutation matrix of `σ`. -/
def pmat {X : Type} [DecidableEq X] (σ : X ≃ X) : Matrix X X ℂ :=
  Matrix.of fun a b => if a = σ b then 1 else 0

theorem pmat_refl {X : Type} [DecidableEq X] : pmat (Equiv.refl X) = 1 := by
  ext a b
  simp only [pmat, of_apply, Equiv.refl_apply, one_apply]
  split_ifs <;> simp_all

theorem pmat_iso {X : Type} [Fintype X] [DecidableEq X] (σ : X ≃ X) : (pmat σ)ᴴ * pmat σ = 1 := by
  ext a b
  simp only [mul_apply, conjTranspose_apply, pmat, of_apply, one_apply]
  rw [Finset.sum_eq_single (σ a)]
  · simp only [if_true, star_one, one_mul, EmbeddingLike.apply_eq_iff_eq]
  · intro c _ hc; rw [if_neg hc, star_zero, zero_mul]
  · simp

theorem tv_pmat (k : ℕ) (σ : Reg e k × Mem ≃ Reg e k × Mem) (v : Qubits e.totalWires × Mem → ℂ)
    (y : Qubits e.totalWires) (μ' : Mem) :
    tv k (pmat σ) v (y, μ') = v (PrefixData.regSet e k y (σ.symm ((wireSplitE e k y).2, μ')).1,
      (σ.symm ((wireSplitE e k y).2, μ')).2) := by
  rw [tv_apply, ← Fintype.sum_prod_type', Finset.sum_eq_single (σ.symm ((wireSplitE e k y).2, μ'))]
  · simp [pmat]
  · intro b _ hb
    rw [pmat, of_apply, if_neg, zero_mul]
    intro h
    exact hb (by rw [h, Equiv.symm_apply_apply])
  · simp

end TV

/-! ## Forms: the actual wires carry `P`, a virtual copy carries the rest -/

section Form

variable {N : Type} [Fintype N] [DecidableEq N]

/-- Merge the actual wires on `P` with the virtual wires off `P`. -/
def mergeP (P : Fin d.totalWires → Prop) [DecidablePred P] (y z : Qubits d.totalWires) :
    Qubits d.totalWires := fun w => if P w then y w else z w

/-- The simulating state of a generalized state `v`. -/
noncomputable def form (P : Fin d.totalWires → Prop) [DecidablePred P]
    (v : Qubits d.totalWires × N → ℂ) : Qubits d.totalWires × (Qubits d.totalWires × N) → ℂ :=
  fun p => (if (∀ w, ¬ P w → p.1 w = false) ∧ (∀ w, P w → p.2.1 w = false) then 1 else 0) *
    v (mergeP P p.1 p.2.1, p.2.2)

theorem regSet_self (k : ℕ) (z : Qubits d.totalWires) :
    PrefixData.regSet d k z (wireSplitE d k z).2 = z := by
  funext w; rw [PrefixData.regSet_apply]; split_ifs <;> rfl

/-- Swap register `k` between the actual wires and the virtual copy. -/
def σswap (k : ℕ) : Reg d k × (Qubits d.totalWires × N) ≃ Reg d k × (Qubits d.totalWires × N) where
  toFun p := ((wireSplitE d k p.2.1).2, (PrefixData.regSet d k p.2.1 p.1, p.2.2))
  invFun p := ((wireSplitE d k p.2.1).2, (PrefixData.regSet d k p.2.1 p.1, p.2.2))
  left_inv p := by
    obtain ⟨g, z, ν⟩ := p
    simp only [regSet_snd, regSet_regSet, regSet_self]
  right_inv p := by
    obtain ⟨g, z, ν⟩ := p
    simp only [regSet_snd, regSet_regSet, regSet_self]

theorem regSet_apply' (k : ℕ) (y z : Qubits d.totalWires) (w : Fin d.totalWires) :
    PrefixData.regSet d k y (wireSplitE d k z).2 w = if inReg d k w then z w else y w := by
  rw [PrefixData.regSet_apply]; split_ifs <;> rfl

/-- **Swapping a register moves it between the actual and the virtual part.** -/
theorem tv_swap_form (k : ℕ) (P P' : Fin d.totalWires → Prop) [DecidablePred P] [DecidablePred P']
    (hP : ∀ w, P' w ↔ (if inReg d k w then ¬ P w else P w)) (v : Qubits d.totalWires × N → ℂ) :
    tv k (pmat (σswap (N := N) k)) (form P v) = form P' v := by
  funext ⟨y, z', ν'⟩
  rw [tv_pmat]
  change form P v (PrefixData.regSet d k y (wireSplitE d k z').2,
    (PrefixData.regSet d k z' (wireSplitE d k y).2, ν')) = form P' v (y, (z', ν'))
  simp only [form, regSet_apply']
  have hm : mergeP P (PrefixData.regSet d k y (wireSplitE d k z').2)
      (PrefixData.regSet d k z' (wireSplitE d k y).2) = mergeP P' y z' := by
    funext w
    simp only [mergeP, regSet_apply', hP w]
    split_ifs <;> simp_all
  have hc : ((∀ w, ¬ P w → (if inReg d k w then z' w else y w) = false) ∧
      (∀ w, P w → (if inReg d k w then y w else z' w) = false)) ↔
      ((∀ w, ¬ P' w → y w = false) ∧ (∀ w, P' w → z' w = false)) := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rw [hP w] at hw
        by_cases hr : inReg d k w
        · rw [if_pos hr] at hw; have := h2 w (not_not.mp hw); rwa [if_pos hr] at this
        · rw [if_neg hr] at hw; have := h1 w hw; rwa [if_neg hr] at this
      · rw [hP w] at hw
        by_cases hr : inReg d k w
        · rw [if_pos hr] at hw; have := h1 w hw; rwa [if_pos hr] at this
        · rw [if_neg hr] at hw; have := h2 w hw; rwa [if_neg hr] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · by_cases hr : inReg d k w
        · rw [if_pos hr]; exact h2 w ((hP w).mpr (by rw [if_pos hr]; exact hw))
        · rw [if_neg hr]; exact h1 w (fun h => by rw [hP w, if_neg hr] at h; exact hw h)
      · by_cases hr : inReg d k w
        · rw [if_pos hr]; exact h1 w (fun h => by rw [hP w, if_pos hr] at h; exact h hw)
        · rw [if_neg hr]; exact h2 w ((hP w).mpr (by rw [if_neg hr]; exact hw))
  rw [hm]
  congr 1
  exact if_congr hc rfl rfl

omit [Fintype N] [DecidableEq N] in
theorem gsplit_symm_apply (k : ℕ) (a : KS d k) (b : PS d k) (ν : N) :
    (gsplit d k N).symm (a, (b, ν)) =
      (fun w => if h : kept d k w then a ⟨w, h⟩ else b ⟨w, h⟩, ν) := by
  simp [gsplit]
  funext w
  rfl

omit [Fintype N] [DecidableEq N] in
theorem gsplit_apply (k : ℕ) (z : Qubits d.totalWires) (ν : N) :
    gsplit d k N (z, ν) = ((fun w => z w.1), ((fun w => z w.1), ν)) := rfl

end Form

section Sim

variable (G : GProver d)

/-- The generalized unitary, acting on the virtual copy and the memory. -/
noncomputable def UL (k : ℕ) :
    Matrix (Reg d k × (Qubits d.totalWires × G.N)) (Reg d k × (Qubits d.totalWires × G.N)) ℂ :=
  ((1 : Matrix (Reg d k) (Reg d k) ℂ) ⊗ₖ ((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ G.U k)).submatrix
    ((Equiv.refl _).prodCongr (gsplit d k G.N)) ((Equiv.refl _).prodCongr (gsplit d k G.N))

/-- **The generalized unitary on the virtual copy is the generalized turn.** -/
theorem tv_UL (k : ℕ) (v : Qubits d.totalWires × G.N → ℂ) :
    tv k (UL G k) (form (kept d k) v) = form (kept d k) (gturn G k v) := by
  funext ⟨y, z', ν'⟩
  rw [tv_apply, Finset.sum_eq_single (wireSplitE d k y).2]
  · rw [regSet_self]
    simp only [UL, submatrix_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id,
      kroneckerMap_apply, one_apply, if_true, one_mul]
    rw [← Fintype.sum_equiv (gsplit d k G.N).symm (fun q => ((if (gsplit d k G.N (z', ν')).1 =
      q.1 then (1 : ℂ) else 0) * G.U k (gsplit d k G.N (z', ν')).2 q.2) *
        form (kept d k) v (y, (gsplit d k G.N).symm q)) _ (fun q => by
          rw [Equiv.apply_symm_apply])]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (gsplit d k G.N (z', ν')).1]
    · simp only [if_true, one_mul]
      simp only [form, gturn, Function.comp_apply]
      rw [show gsplit d k G.N (mergeP (kept d k) y z', ν') =
        ((gsplit d k G.N (y, ν')).1, ((gsplit d k G.N (z', ν')).2)) by
          rw [gsplit_apply, gsplit_apply, gsplit_apply]
          congr 1
          · funext w; simp [mergeP, w.2]
          · congr 1; funext w; simp [mergeP, w.2], one_kron_mulVec_apply]
      simp only [mulVec, dotProduct]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      obtain ⟨b, ν⟩ := q
      simp only [Function.comp_apply, gsplit_symm_apply, gsplit_apply]
      have hcond : ((∀ w, ¬ kept d k w → y w = false) ∧
          ∀ w, kept d k w → (if h : kept d k w then z' w else b ⟨w, h⟩) = false) ↔
          ((∀ w, ¬ kept d k w → y w = false) ∧ ∀ w, kept d k w → z' w = false) := by
        refine and_congr Iff.rfl (forall_congr' fun w => forall_congr' fun hw => ?_)
        rw [dif_pos hw]
      rw [if_congr hcond rfl rfl]
      have hmerge : mergeP (kept d k) y (fun w => if h : kept d k w then z' w else b ⟨w, h⟩) =
          fun w => if h : kept d k w then y w else b ⟨w, h⟩ := by
        funext w; simp only [mergeP]; split_ifs <;> rfl
      rw [hmerge]
      ring
    · intro a _ ha
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [if_neg (Ne.symm ha)]
      ring
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun μ _ => ?_
    simp [UL, kroneckerMap_apply, one_apply, Ne.symm hx]
  · simp

theorem kronU_iso (k : ℕ) :
    ((1 : Matrix (Reg d k) (Reg d k) ℂ) ⊗ₖ ((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ G.U k))ᴴ *
      ((1 : Matrix (Reg d k) (Reg d k) ℂ) ⊗ₖ ((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ G.U k)) = 1 := by
  have hU := Matrix.mem_unitaryGroup_iff'.mp (G.unit k)
  rw [conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one, conjTranspose_one,
    ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  change (1 : Matrix (Reg d k) (Reg d k) ℂ) ⊗ₖ ((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ (star (G.U k) * G.U k)) = 1
  rw [hU, one_kronecker_one, one_kronecker_one]

theorem UL_iso (k : ℕ) : (UL G k)ᴴ * UL G k = 1 := by
  unfold UL
  rw [conjTranspose_submatrix, submatrix_mul_equiv, kronU_iso]
  exact submatrix_one_equiv _

/-- The swap before the generalized unitary (messages to the prover). -/
def σin (k : ℕ) : Reg d k × (Qubits d.totalWires × G.N) ≃ Reg d k × (Qubits d.totalWires × G.N) :=
  if toProverAt d k then σswap k else Equiv.refl _

/-- The swap after the generalized unitary (messages to the verifier). -/
def σout (k : ℕ) : Reg d k × (Qubits d.totalWires × G.N) ≃ Reg d k × (Qubits d.totalWires × G.N) :=
  if toProverAt d k then Equiv.refl _ else σswap k

/-- **The simulating turn.** -/
noncomputable def simV (k : ℕ) :
    Matrix (Reg d k × (Qubits d.totalWires × G.N)) (Reg d k × (Qubits d.totalWires × G.N)) ℂ :=
  pmat (σout G k) * UL G k * pmat (σin G k)

theorem simV_iso (k : ℕ) : (simV G k)ᴴ * simV G k = 1 := by
  simp only [simV, conjTranspose_mul]
  rw [show (pmat (σin G k))ᴴ * ((UL G k)ᴴ * (pmat (σout G k))ᴴ) *
      (pmat (σout G k) * UL G k * pmat (σin G k)) = (pmat (σin G k))ᴴ * ((UL G k)ᴴ *
        ((pmat (σout G k))ᴴ * pmat (σout G k)) * UL G k) * pmat (σin G k) by
      simp only [Matrix.mul_assoc],
    pmat_iso, Matrix.mul_one, UL_iso, Matrix.mul_one, pmat_iso]

end Sim

/-! ## Which wires change hands at a turn -/

section Held

theorem held_succ_iff_of_not_reg {k : ℕ} {x : Fin d.totalWires} (hx : ¬ inReg d k x) :
    d.held (k + 1) x = true ↔ d.held k x = true := by
  rw [held_iff, held_iff]
  refine or_congr Iff.rfl ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, ?_⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, ?_⟩⟩
  · have hik : i ≠ k := fun e => hx (e ▸ hi)
    cases hdir : (d.msgs.map Message.dir).getD i .toVerifier <;> rw [hdir] at h <;>
      simp [dirOk] at h ⊢ <;> omega
  · have hik : i ≠ k := fun e => hx (e ▸ hi)
    cases hdir : (d.msgs.map Message.dir).getD i .toVerifier <;> rw [hdir] at h <;>
      simp [dirOk] at h ⊢ <;> omega

theorem not_priv_of_inReg {k : ℕ} {x : Fin d.totalWires} (hx : inReg d k x) : ¬ (x : ℕ) < d.priv := by
  have : d.priv ≤ d.msgOffset k := by simp [Desc.msgOffset]
  have := hx.1
  omega

theorem held_reg_toP {k : ℕ} (hp : toProverAt d k) {x : Fin d.totalWires} (hx : inReg d k x) :
    d.held k x = true ∧ d.held (k + 1) x = false := by
  constructor
  · rw [held_iff]
    right
    exact ⟨k, hx, by unfold toProverAt at hp; rw [hp]; simp [dirOk]⟩
  · rw [Bool.eq_false_iff, ne_eq, held_iff]
    rintro (h | ⟨i, hi, h⟩)
    · exact not_priv_of_inReg hx h
    · obtain rfl := inReg_unique hi hx
      unfold toProverAt at hp; rw [hp] at h; simp [dirOk] at h

theorem held_reg_toV {k : ℕ} (hp : ¬ toProverAt d k) {x : Fin d.totalWires} (hx : inReg d k x) :
    d.held k x = false ∧ d.held (k + 1) x = true := by
  have hk := lt_numMsgs_of_inReg hx
  have hv : (d.msgs.map Message.dir).getD k .toVerifier = .toVerifier := by
    unfold toProverAt at hp
    cases h : (d.msgs.map Message.dir).getD k .toVerifier
    · rfl
    · exact absurd h hp
  constructor
  · rw [Bool.eq_false_iff, ne_eq, held_iff]
    rintro (h | ⟨i, hi, h⟩)
    · exact not_priv_of_inReg hx h
    · obtain rfl := inReg_unique hi hx
      rw [hv] at h; simp [dirOk] at h
  · rw [held_iff]
    right
    exact ⟨k, hx, by rw [hv]; simp [dirOk]⟩

/-- Messages to the prover: the swap takes `held k` to `kept k`. -/
theorem kept_iff_toP {k : ℕ} (hp : toProverAt d k) (w : Fin d.totalWires) :
    kept d k w ↔ (if inReg d k w then ¬ d.held k w = true else d.held k w = true) := by
  unfold kept
  split_ifs with hw
  · have := held_reg_toP hp hw
    simp [this.1, this.2]
  · rw [held_succ_iff_of_not_reg hw, and_self]

theorem kept_iff_held_succ_toP {k : ℕ} (hp : toProverAt d k) (w : Fin d.totalWires) :
    kept d k w ↔ d.held (k + 1) w = true := by
  unfold kept
  by_cases hw : inReg d k w
  · have := held_reg_toP hp hw
    simp [this.1, this.2]
  · rw [held_succ_iff_of_not_reg hw, and_self]

theorem kept_iff_held_toV {k : ℕ} (hp : ¬ toProverAt d k) (w : Fin d.totalWires) :
    kept d k w ↔ d.held k w = true := by
  unfold kept
  by_cases hw : inReg d k w
  · have := held_reg_toV hp hw
    simp [this.1, this.2]
  · rw [held_succ_iff_of_not_reg hw, and_self]

/-- Messages to the verifier: the swap takes `kept k` to `held (k + 1)`. -/
theorem held_succ_iff_toV {k : ℕ} (hp : ¬ toProverAt d k) (w : Fin d.totalWires) :
    d.held (k + 1) w = true ↔ (if inReg d k w then ¬ kept d k w else kept d k w) := by
  split_ifs with hw
  · have := held_reg_toV hp hw
    simp [kept, this.1, this.2]
  · rw [kept_iff_held_toV hp, held_succ_iff_of_not_reg hw]

end Held

/-! ## The simulation -/

section Run

variable {N : Type} [Fintype N] [DecidableEq N]

omit [Fintype N] [DecidableEq N] in
theorem form_congr {P P' : Fin d.totalWires → Prop} [DecidablePred P] [DecidablePred P']
    (h : ∀ w, P w ↔ P' w) (v : Qubits d.totalWires × N → ℂ) : form P v = form P' v := by
  funext p
  simp only [form, mergeP]
  congr 1
  · exact if_congr (and_congr (forall_congr' fun w => imp_congr (not_congr (h w)) Iff.rfl)
      (forall_congr' fun w => imp_congr (h w) Iff.rfl)) rfl rfl
  · congr 2; funext w; exact if_congr (h w) rfl rfl

theorem tv_one (k : ℕ) (v : Qubits d.totalWires × (Qubits d.totalWires × N) → ℂ) :
    tv k (1 : Matrix (Reg d k × (Qubits d.totalWires × N)) _ ℂ) v = v := by
  funext p
  simp [tv, one_kronecker_one]

/-- **A verifier block on a simulating state.** -/
theorem block_form (hd : d.Valid) (j : ℕ) (v : Qubits d.totalWires × N → ℂ) :
    (blockMat d j ⊗ₖ (1 : Matrix (Qubits d.totalWires × N) (Qubits d.totalWires × N) ℂ)) *ᵥ
      form (fun w => d.held j w = true) v =
        form (fun w => d.held j w = true)
          ((blockMat d j ⊗ₖ (1 : Matrix N N ℂ)) *ᵥ v) := by
  funext ⟨y, z, ν⟩
  rw [kronOne_mulVec_apply]
  simp only [form]
  rw [kronOne_mulVec_apply, blockMat, layerMat_mulVec, layerMat_mulVec]
  have hl : ∀ g ∈ (d.blocks.getD j []).filterMap (Gate.toInstr? d.totalWires),
      ∀ w ∈ g.support, ¬ (fun w => ¬ d.held j w = true) w := by
    intro g hg w hw h
    exact h (hd.support_held j g hg w hw)
  have key := runLayer_comp (fun w => ¬ d.held j w = true)
    (fun y' => mergeP (fun w => d.held j w = true) y' z)
    (fun y' i b hi => by
      funext w; simp only [mergeP, Function.update_apply]
      split_ifs <;> simp_all)
    (fun y' i hi => by simp only [mergeP]; simp at hi; simp [hi])
    (fun y' => if (∀ w : Fin d.totalWires, ¬ d.held j w = true → y' w = false) ∧
      (∀ w : Fin d.totalWires, d.held j w = true → z w = false) then (1 : ℂ) else 0)
    (fun y' i b hi => by
      have hi' : d.held j i = true := by simpa using hi
      refine if_congr (and_congr (forall_congr' fun w => forall_congr' fun hw => ?_) Iff.rfl) rfl rfl
      rw [Function.update_of_ne (fun e : w = i => hw (by rw [e]; exact hi'))])
    _ hl (fun y'' => v (y'', ν))
  exact congrFun key y

theorem sum_form_merge (P : Fin d.totalWires → Prop) [DecidablePred P]
    (F : Qubits d.totalWires → ℝ) :
    ∑ y, ∑ z, (if (∀ w, ¬ P w → y w = false) ∧ (∀ w, P w → z w = false) then
      F (mergeP P y z) else 0) = ∑ y, F y := by
  rw [← Fintype.sum_prod_type' (f := fun y z => if (∀ w, ¬ P w → y w = false) ∧
    (∀ w, P w → z w = false) then F (mergeP P y z) else 0), ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun p => mergeP P p.1 p.2)
    (fun y => (fun w => if P w then y w else false, fun w => if P w then false else y w))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro y _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun w hw => by simp [hw], fun w hw => by simp [hw]⟩
  · rintro ⟨y, z⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp only [mergeP]; split_ifs with h
      · rfl
      · exact (hp.1 w h).symm
    · simp only [mergeP]; split_ifs with h
      · exact (hp.2 w h).symm
      · rfl
  · intro y _
    funext w
    simp only [mergeP]
    split_ifs <;> rfl

end Run

section Legal

variable (G : GProver d) (ξ₀ : Qubits d.totalWires × G.N → ℂ)

/-- **The legal prover simulating a generalized prover**, keeping a virtual copy of the wires. -/
@[reducible] noncomputable def simT (hξ : GInit d ξ₀) : IsoStrategy (Reg d) (Reg d) d.numMsgs where
  M _ := Qubits d.totalWires × G.N
  init := ξ₀
  init_density := by rw [isDensity_pure_iff, Fintype.sum_prod_type]; exact hξ.1
  V k := simV G k
  V_iso k _ := simV_iso G k

theorem turnVec_simT (hξ : GInit d ξ₀) (k : ℕ) (g : Qubits d.totalWires × G.N → ℂ) :
    turnVec (simT G ξ₀ hξ) k (form (fun w => d.held k w = true) g) =
      form (fun w => d.held (k + 1) w = true) (gturn G k g) := by
  change tv k (simV G k) _ = _
  rw [simV, tv_mul, tv_mul]
  by_cases hp : toProverAt d k
  · have h1 : σin G k = σswap k := by unfold σin; rw [if_pos hp]
    have h2 : σout G k = Equiv.refl _ := by unfold σout; rw [if_pos hp]
    rw [h1, h2, tv_swap_form k _ (kept d k) (kept_iff_toP hp), tv_UL, pmat_refl, tv_one]
    exact form_congr (kept_iff_held_succ_toP hp) _
  · have h1 : σin G k = Equiv.refl _ := by unfold σin; rw [if_neg hp]
    have h2 : σout G k = σswap k := by unfold σout; rw [if_neg hp]
    rw [h1, h2, pmat_refl, tv_one, form_congr (fun w => (kept_iff_held_toV hp w).symm), tv_UL,
      tv_swap_form k (kept d k) _ (held_succ_iff_toV hp)]

theorem init_form (hξ : GInit d ξ₀) :
    (fun p : Qubits d.totalWires × (Qubits d.totalWires × G.N) => zeroVec _ p.1 * ξ₀ p.2) =
      form (fun w => d.held 0 w = true) ξ₀ := by
  funext ⟨y, z, ν⟩
  simp only [form, zeroVec]
  by_cases hy : y = Qubits.zero _
  · subst hy
    rw [if_pos rfl, one_mul]
    by_cases hz : ∀ w : Fin d.totalWires, d.held 0 w = true → z w = false
    · rw [if_pos ⟨fun w _ => rfl, hz⟩, one_mul]
      congr 2
      funext w; simp only [mergeP]; split_ifs with h
      · show z w = false; exact hz w h
      · rfl
    · rw [if_neg (fun h => hz h.2), zero_mul]
      push Not at hz
      obtain ⟨w, hw, hzw⟩ := hz
      exact hξ.2 z ν ⟨w, hw, by simpa using hzw⟩
  · rw [if_neg hy, zero_mul]
    by_cases hc : (∀ w : Fin d.totalWires, ¬ d.held 0 w = true → y w = false) ∧
        ∀ w : Fin d.totalWires, d.held 0 w = true → z w = false
    · rw [if_pos hc, one_mul]
      have : ∃ w, y w = true := by
        by_contra h
        push Not at h
        exact hy (funext fun w => by show y w = false; simpa using h w)
      obtain ⟨w, hw⟩ := this
      have hh : d.held 0 w = true := by
        by_contra h; rw [hc.1 w h] at hw; exact Bool.noConfusion hw
      refine (hξ.2 _ ν ⟨w, hh, ?_⟩).symm
      simp only [mergeP, if_pos hh]; exact hw
    · rw [if_neg hc, zero_mul]

/-- **The simulation runs the generalized prover.** -/
theorem pureRun_simT (hd : d.Valid) (hξ : GInit d ξ₀) : ∀ j,
    pureRun (simT G ξ₀ hξ) j = form (fun w => d.held j w = true) (gRun G ξ₀ j)
  | 0 => by
    rw [pureRun, gRun]
    change (blockMat d 0 ⊗ₖ (1 : Matrix (Qubits d.totalWires × G.N) _ ℂ)) *ᵥ
      (fun p => zeroVec _ p.1 * ξ₀ p.2) = _
    rw [init_form G ξ₀ hξ, block_form hd]
  | j + 1 => by
    rw [pureRun, gRun, pureRun_simT hd hξ j, turnVec_simT, block_form hd]

theorem outBit_mergeP (hd : d.Valid) (y z : Qubits d.totalWires) :
    outBit d (mergeP (fun w => d.held d.numMsgs w = true) y z) ↔ outBit d y := by
  have ho := hd.out_lt
  have hh : d.held d.numMsgs d.out = true := by simp [Desc.held, ho]
  constructor
  · rintro ⟨h, e⟩; refine ⟨h, ?_⟩; simpa [mergeP, hh] using e
  · rintro ⟨h, e⟩; refine ⟨h, ?_⟩; simpa [mergeP, hh] using e

/-- **Generalized provers do no better than legal provers.** -/
theorem gAcc_le_value (hd : d.Valid) (hξ : GInit d ξ₀) : gAcc G ξ₀ ≤ value d := by
  have h : accept (simT G ξ₀ hξ).toOp = gAcc G ξ₀ := by
    rw [accept_pureRun, accept_expect, pureRun_simT G ξ₀ hd hξ, gAcc]
    simp only [Fintype.sum_prod_type]
    conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun y ν => if outBit d y then
      ‖gRun G ξ₀ d.numMsgs (y, ν)‖ ^ 2 else 0)]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← sum_form_merge (fun w => d.held d.numMsgs w = true) (fun y' => if outBit d y' then
      ‖gRun G ξ₀ d.numMsgs (y', ν)‖ ^ 2 else 0)]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    simp only [form]
    by_cases hc : (∀ w : Fin d.totalWires, ¬ d.held d.numMsgs w = true → y w = false) ∧
        ∀ w : Fin d.totalWires, d.held d.numMsgs w = true → z w = false
    · rw [if_pos hc, if_pos hc, one_mul]
      by_cases ho : outBit d y
      · rw [if_pos ho, if_pos ((outBit_mergeP hd y z).mpr ho)]
      · rw [if_neg ho, if_neg (fun h => ho ((outBit_mergeP hd y z).mp h))]
    · rw [if_neg hc, if_neg hc, zero_mul, norm_zero]
      simp
  rw [← h]
  exact accept_le_value d _

end Legal

end ShiQIP
