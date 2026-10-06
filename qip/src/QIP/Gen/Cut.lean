/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Gen.Model
import Quantum.UhlmannAttained
import Quantum.FidelityTwoTargets

/-!
# Q30 — cut states and stitching

For a description `d`, a memory `N` and unitary turn families, the generalized run is a product of
unitaries on `Qubits × N` (`blockOp`, `turnOp`, `preOp`, `sufOp`, `gRun_eq_preOp`). Fix a cut
after block `c`, and a unit cut state `ξ`.

* `fwdP`: the second half accepts; `bwdP`: undoing the first half returns to `|0⟩`.
* **`fwd_overlap`**: for a unitary `W` and a projection `P`, `ξ_F = W† P W ξ / √p` is a unit
  vector accepted with certainty with `⟨ξ, ξ_F⟩ = √p`.
* **`fwd_bound`**, **`bwd_bound`**: `fwdP ≤ F(ξ_K, ρ_F)²` with `ρ_F` accepted with certainty,
  `bwdP ≤ F(ξ_K, ρ_B)²` with `ρ_B` reachable from a legal initial state (`K`: the wires kept
  across turn `c`, `margK`).
* **`stitch`**: `F(ρ_B, ρ_F)² ≤ value d`. The stitched generalized prover runs the prefix, an
  Uhlmann unitary on everything outside `K` (`exists_unitary_overlap_eq_fidelity`, with an
  ancilla), then the suffix; `gAcc_le_value` bounds it.
* **`cut_bound`**: `fwdP + bwdP ≤ 1 + √(value d)`, by `fidelity_two_targets` (Q12). Empty cases
  (`p = 0` or `q = 0`) are handled explicitly.
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {d : Desc} {N : Type} [Fintype N] [DecidableEq N]

/-! ## Operators -/

variable (d N) in
/-- Verifier block `j` on wires and memory. -/
noncomputable def blockOp (j : ℕ) : Matrix (Qubits d.totalWires × N) (Qubits d.totalWires × N) ℂ :=
  blockMat d j ⊗ₖ (1 : Matrix N N ℂ)

/-- A generalized turn, as a matrix. -/
noncomputable def turnOp {k : ℕ} (U : Matrix (PS d k × N) (PS d k × N) ℂ) :
    Matrix (Qubits d.totalWires × N) (Qubits d.totalWires × N) ℂ :=
  ((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ U).submatrix (gsplit d k N) (gsplit d k N)

/-- Turn families. -/
abbrev Turns (d : Desc) (N : Type) : Type := ∀ k, Matrix (PS d k × N) (PS d k × N) ℂ

/-- The run up to block `j`, as a matrix. -/
noncomputable def preOp (U : Turns d N) : ℕ → Matrix (Qubits d.totalWires × N) (Qubits d.totalWires × N) ℂ
  | 0 => blockOp d N 0
  | j + 1 => blockOp d N (j + 1) * turnOp (U j) * preOp U j

/-- The run from block `c` to block `c + j`. -/
noncomputable def sufOp (U : Turns d N) (c : ℕ) :
    ℕ → Matrix (Qubits d.totalWires × N) (Qubits d.totalWires × N) ℂ
  | 0 => 1
  | j + 1 => blockOp d N (c + j + 1) * turnOp (U (c + j)) * sufOp U c j

theorem preOp_add (U : Turns d N) (c : ℕ) : ∀ j, preOp U (c + j) = sufOp U c j * preOp U c
  | 0 => by rw [sufOp, Matrix.one_mul]; rfl
  | j + 1 => by
    change blockOp d N (c + j + 1) * turnOp (U (c + j)) * preOp U (c + j) = _
    rw [preOp_add U c j, sufOp]
    simp only [Matrix.mul_assoc]

theorem gturn_eq (G : GProver d) (k : ℕ) (v : Qubits d.totalWires × G.N → ℂ) :
    gturn G k v = turnOp (G.U k) *ᵥ v := by
  rw [turnOp, submatrix_mulVec_equiv]
  rfl

/-- **Generalized runs are products of unitaries.** -/
theorem gRun_eq_preOp (G : GProver d) (ξ₀ : Qubits d.totalWires × G.N → ℂ) :
    ∀ j, gRun G ξ₀ j = preOp G.U j *ᵥ ξ₀
  | 0 => rfl
  | j + 1 => by
    rw [gRun, gRun_eq_preOp G ξ₀ j, gturn_eq, preOp, mulVec_mulVec, mulVec_mulVec]
    rfl

theorem blockOp_mem (j : ℕ) : blockOp d N j ∈ Matrix.unitaryGroup (Qubits d.totalWires × N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h := Matrix.mem_unitaryGroup_iff'.mp (blockMat_mem_unitaryGroup d j)
  change (blockMat d j ⊗ₖ (1 : Matrix N N ℂ))ᴴ * (blockMat d j ⊗ₖ (1 : Matrix N N ℂ)) = 1
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  change (star (blockMat d j) * blockMat d j) ⊗ₖ (1 : Matrix N N ℂ) = 1
  rw [h, one_kronecker_one]

theorem turnOp_mem {k : ℕ} {U : Matrix (PS d k × N) (PS d k × N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (PS d k × N) ℂ) :
    turnOp U ∈ Matrix.unitaryGroup (Qubits d.totalWires × N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (turnOp U)ᴴ * turnOp U = 1
  rw [turnOp, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]
  change ((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ (star U * U)).submatrix _ _ = 1
  rw [Matrix.mem_unitaryGroup_iff'.mp hU, one_kronecker_one]
  exact submatrix_one_equiv _

theorem preOp_mem (U : Turns d N) (hU : ∀ k, U k ∈ Matrix.unitaryGroup (PS d k × N) ℂ) :
    ∀ j, preOp U j ∈ Matrix.unitaryGroup (Qubits d.totalWires × N) ℂ
  | 0 => blockOp_mem 0
  | j + 1 => Submonoid.mul_mem _ (Submonoid.mul_mem _ (blockOp_mem _) (turnOp_mem (hU j)))
      (preOp_mem U hU j)

theorem sufOp_mem (U : Turns d N) (hU : ∀ k, U k ∈ Matrix.unitaryGroup (PS d k × N) ℂ) (c : ℕ) :
    ∀ j, sufOp U c j ∈ Matrix.unitaryGroup (Qubits d.totalWires × N) ℂ
  | 0 => Submonoid.one_mem _
  | j + 1 => Submonoid.mul_mem _ (Submonoid.mul_mem _ (blockOp_mem _) (turnOp_mem (hU _)))
      (sufOp_mem U hU c j)

/-! ## Vectors -/

section Vec

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The squared norm. -/
noncomputable def nsq (v : X → ℂ) : ℝ := ∑ x, ‖v x‖ ^ 2

omit [DecidableEq X] in
theorem dot_self_eq_nsq (v : X → ℂ) : star v ⬝ᵥ v = ((nsq v : ℝ) : ℂ) := by
  rw [nsq, dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [DecidableEq X] in
theorem nsq_nonneg (v : X → ℂ) : 0 ≤ nsq v := Finset.sum_nonneg fun _ _ => by positivity

omit [DecidableEq X] in
theorem dot_mulVec_adj (A : Matrix X X ℂ) (u v : X → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = star (Aᴴ *ᵥ u) ⬝ᵥ v := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

theorem nsq_unitary {W : Matrix X X ℂ} (hW : W ∈ Matrix.unitaryGroup X ℂ) (v : X → ℂ) :
    nsq (W *ᵥ v) = nsq v := by
  have h := congrArg Complex.re (dot_self_eq_nsq (W *ᵥ v))
  rw [dot_mulVec_adj, mulVec_mulVec,
    show Wᴴ * W = 1 from Matrix.mem_unitaryGroup_iff'.mp hW, one_mulVec, dot_self_eq_nsq] at h
  simpa using h.symm

omit [DecidableEq X] in
theorem nsq_smul (a : ℂ) (v : X → ℂ) : nsq (a • v) = ‖a‖ ^ 2 * nsq v := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

/-- **The accepted part, normalized.** For a unitary `W` and a projection `P`, with
`p = ‖P W ξ‖² > 0`, the state `W† P W ξ / √p` is a unit vector accepted with certainty, with
overlap `√p` with `ξ`. -/
theorem fwd_overlap {W P : Matrix X X ℂ} (hW : W ∈ Matrix.unitaryGroup X ℂ) (hPs : Pᴴ = P)
    (hPP : P * P = P) (ξ : X → ℂ) (hp : 0 < nsq (P *ᵥ (W *ᵥ ξ))) :
    nsq (((Real.sqrt (nsq (P *ᵥ (W *ᵥ ξ))))⁻¹ : ℂ) • (Wᴴ *ᵥ (P *ᵥ (W *ᵥ ξ)))) = 1 ∧
      P *ᵥ (W *ᵥ (((Real.sqrt (nsq (P *ᵥ (W *ᵥ ξ))))⁻¹ : ℂ) • (Wᴴ *ᵥ (P *ᵥ (W *ᵥ ξ))))) =
        W *ᵥ (((Real.sqrt (nsq (P *ᵥ (W *ᵥ ξ))))⁻¹ : ℂ) • (Wᴴ *ᵥ (P *ᵥ (W *ᵥ ξ)))) ∧
      star ξ ⬝ᵥ (((Real.sqrt (nsq (P *ᵥ (W *ᵥ ξ))))⁻¹ : ℂ) • (Wᴴ *ᵥ (P *ᵥ (W *ᵥ ξ)))) =
        ((Real.sqrt (nsq (P *ᵥ (W *ᵥ ξ))) : ℝ) : ℂ) := by
  set p := nsq (P *ᵥ (W *ᵥ ξ)) with hpdef
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hWW : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have hWv : W *ᵥ (((Real.sqrt p)⁻¹ : ℂ) • (Wᴴ *ᵥ (P *ᵥ (W *ᵥ ξ)))) =
      ((Real.sqrt p)⁻¹ : ℂ) • (P *ᵥ (W *ᵥ ξ)) := by
    rw [mulVec_smul, mulVec_mulVec, hWW, one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · rw [← nsq_unitary hW, hWv, nsq_smul, ← hpdef]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, inv_pow,
      Real.sq_sqrt hp.le]
    field_simp
  · rw [hWv, mulVec_smul, mulVec_mulVec, hPP]
  · rw [dotProduct_smul, dot_mulVec_adj, conjTranspose_conjTranspose]
    have : star (W *ᵥ ξ) ⬝ᵥ (P *ᵥ (W *ᵥ ξ)) = ((p : ℝ) : ℂ) := by
      rw [← hPP, ← mulVec_mulVec, dot_mulVec_adj, hPs, dot_self_eq_nsq]
    rw [this, smul_eq_mul, show ((p : ℝ) : ℂ) = ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]]
    have : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp

end Vec

/-! ## The reduced state on the wires kept at the cut -/

variable (N) in
/-- The reduced state on the wires kept across turn `c`; its purifying system is exactly what
the prover acts on at that turn. -/
noncomputable def margK (c : ℕ) (ξ : Qubits d.totalWires × N → ℂ) : Matrix (KS d c) (KS d c) ℂ :=
  traceRight (pureState (ξ ∘ (gsplit d c N).symm))

omit [DecidableEq N] in
theorem margK_posSemidef (c : ℕ) (ξ : Qubits d.totalWires × N → ℂ) : (margK N c ξ).PosSemidef :=
  posSemidef_traceRight (pureState_posSemidef _)

theorem dot_comp_equiv {X Y : Type} [Fintype X] [Fintype Y] (e : Y ≃ X) (u v : X → ℂ) :
    star (u ∘ e) ⬝ᵥ (v ∘ e) = star u ⬝ᵥ v :=
  Fintype.sum_equiv e _ _ fun _ => rfl

omit [DecidableEq N] in
theorem isDensity_margK (c : ℕ) {ξ : Qubits d.totalWires × N → ℂ} (hξ : nsq ξ = 1) :
    IsDensity (margK N c ξ) := by
  refine ⟨margK_posSemidef c ξ, ?_⟩
  rw [margK, trace_traceRight, trace_pureState]
  have h : nsq (ξ ∘ (gsplit d c N).symm) = 1 := by
    rw [← hξ]; exact Fintype.sum_equiv _ _ _ fun _ => rfl
  exact_mod_cast h

/-- **Overlaps are bounded by the root fidelity of the reduced states at the cut.** -/
theorem norm_dot_le_fidelity (c : ℕ) (ξ η : Qubits d.totalWires × N → ℂ) :
    ‖star ξ ⬝ᵥ η‖ ≤ fidelity (margK N c ξ) (margK N c η) := by
  have := uhlmann_le_general (margK_posSemidef c ξ) (margK_posSemidef c η)
    (rfl : IsPurification (ξ ∘ (gsplit d c N).symm) _)
    (rfl : IsPurification (η ∘ (gsplit d c N).symm) _)
  rwa [dot_comp_equiv] at this

/-! ## Projections -/

section Proj

variable (N) in
/-- The projection onto basis labels with `Q`, memory untouched. -/
noncomputable def projQ (Q : Qubits d.totalWires → Prop) [DecidablePred Q] :
    Matrix (Qubits d.totalWires × N) (Qubits d.totalWires × N) ℂ :=
  basisEffect Q ⊗ₖ (1 : Matrix N N ℂ)

theorem projQ_apply (Q : Qubits d.totalWires → Prop) [DecidablePred Q]
    (v : Qubits d.totalWires × N → ℂ) (y : Qubits d.totalWires) (ν : N) :
    (projQ N Q *ᵥ v) (y, ν) = if Q y then v (y, ν) else 0 := by
  rw [projQ, kronOne_mulVec_apply, basisEffect, mulVec_diagonal]
  split_ifs <;> simp

omit [Fintype N] in
theorem projQ_conjTranspose (Q : Qubits d.totalWires → Prop) [DecidablePred Q] :
    (projQ N Q)ᴴ = projQ N Q := by
  rw [projQ, conjTranspose_kronecker, conjTranspose_one, basisEffect, diagonal_conjTranspose]
  congr 2
  funext y
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem projQ_mul_self (Q : Qubits d.totalWires → Prop) [DecidablePred Q] :
    projQ N Q * projQ N Q = projQ N Q := by
  rw [projQ, ← mul_kronecker_mul, Matrix.one_mul, basisEffect, diagonal_mul_diagonal]
  congr 2
  funext y; split_ifs <;> simp

theorem nsq_projQ (Q : Qubits d.totalWires → Prop) [DecidablePred Q]
    (v : Qubits d.totalWires × N → ℂ) :
    nsq (projQ N Q *ᵥ v) = ∑ y, ∑ ν, if Q y then ‖v (y, ν)‖ ^ 2 else 0 := by
  rw [nsq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [projQ_apply]
  split_ifs <;> simp

/-- **Acceptance of a generalized run.** -/
theorem gAcc_eq_nsq (G : GProver d) (ξ₀ : Qubits d.totalWires × G.N → ℂ) :
    gAcc G ξ₀ = nsq (projQ G.N (outBit d) *ᵥ (preOp G.U d.numMsgs *ᵥ ξ₀)) := by
  rw [nsq_projQ, gAcc, gRun_eq_preOp]

variable (d) in
/-- The wires held during block `0` read `0`. -/
def Zero0 (y : Qubits d.totalWires) : Prop := ∀ w : Fin d.totalWires, d.held 0 w = true → y w = false

instance : DecidablePred (Zero0 d) := fun _ => by unfold Zero0; infer_instance

end Proj

/-! ## The two bounds -/

section Bounds

variable (U : Turns d N) (hU : ∀ k, U k ∈ Matrix.unitaryGroup (PS d k × N) ℂ) (c : ℕ)

/-- The probability that the second half accepts, from the cut state `ξ`. -/
noncomputable def fwdP (ξ : Qubits d.totalWires × N → ℂ) : ℝ :=
  nsq (projQ N (outBit d) *ᵥ (sufOp U c (d.numMsgs - c) *ᵥ ξ))

/-- The probability that undoing the first half returns to `|0⟩`, from the cut state `ξ`. -/
noncomputable def bwdP (ξ : Qubits d.totalWires × N → ℂ) : ℝ :=
  nsq (projQ N (Zero0 d) *ᵥ ((preOp U c)ᴴ *ᵥ ξ))

include hU in
/-- **Forward bound.** -/
theorem fwd_bound (ξ : Qubits d.totalWires × N → ℂ) (hp : 0 < fwdP U c ξ) :
    ∃ ξF, nsq ξF = 1 ∧
      projQ N (outBit d) *ᵥ (sufOp U c (d.numMsgs - c) *ᵥ ξF) = sufOp U c (d.numMsgs - c) *ᵥ ξF ∧
      fwdP U c ξ ≤ fidelity (margK N c ξ) (margK N c ξF) ^ 2 := by
  unfold fwdP at hp ⊢
  obtain ⟨h1, h2, h3⟩ := fwd_overlap (sufOp_mem U hU c _) (projQ_conjTranspose _) (projQ_mul_self _)
    ξ hp
  refine ⟨_, h1, h2, ?_⟩
  have h := norm_dot_le_fidelity c ξ (((Real.sqrt (nsq (projQ N (outBit d) *ᵥ
    (sufOp U c (d.numMsgs - c) *ᵥ ξ))))⁻¹ : ℂ) • ((sufOp U c (d.numMsgs - c))ᴴ *ᵥ
      (projQ N (outBit d) *ᵥ (sufOp U c (d.numMsgs - c) *ᵥ ξ))))
  rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [Real.sq_sqrt hp.le] at this

include hU in
/-- **Backward bound.** -/
theorem bwd_bound (ξ : Qubits d.totalWires × N → ℂ) (hp : 0 < bwdP U c ξ) :
    ∃ ξ₀, GInit d ξ₀ ∧ bwdP U c ξ ≤ fidelity (margK N c ξ) (margK N c (preOp U c *ᵥ ξ₀)) ^ 2 := by
  unfold bwdP at hp ⊢
  have hW : (preOp U c)ᴴ ∈ Matrix.unitaryGroup _ ℂ := conjTranspose_mem_unitaryGroup (preOp_mem U hU c)
  obtain ⟨h1, -, h3⟩ := fwd_overlap hW (projQ_conjTranspose (Zero0 d)) (projQ_mul_self _) ξ hp
  set q := nsq (projQ N (Zero0 d) *ᵥ ((preOp U c)ᴴ *ᵥ ξ)) with hq
  set s : ℂ := ((Real.sqrt q)⁻¹ : ℂ)
  have e : preOp U c *ᵥ (s • (projQ N (Zero0 d) *ᵥ ((preOp U c)ᴴ *ᵥ ξ))) =
      s • ((preOp U c)ᴴᴴ *ᵥ (projQ N (Zero0 d) *ᵥ ((preOp U c)ᴴ *ᵥ ξ))) := by
    rw [conjTranspose_conjTranspose, mulVec_smul]
  refine ⟨s • (projQ N (Zero0 d) *ᵥ ((preOp U c)ᴴ *ᵥ ξ)), ⟨?_, ?_⟩, ?_⟩
  · have hn : nsq (s • (projQ N (Zero0 d) *ᵥ ((preOp U c)ᴴ *ᵥ ξ))) = 1 := by
      rw [nsq_smul, ← hq, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hp.le]
      field_simp
    rw [nsq, Fintype.sum_prod_type] at hn
    exact hn
  · intro y ν ⟨w, hw, hyw⟩
    rw [Pi.smul_apply, projQ_apply, if_neg (fun h => by rw [h w hw] at hyw; exact Bool.noConfusion hyw),
      smul_zero]
  · rw [e]
    have h := norm_dot_le_fidelity c ξ (s • ((preOp U c)ᴴᴴ *ᵥ (projQ N (Zero0 d) *ᵥ
      ((preOp U c)ᴴ *ᵥ ξ))))
    rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt hp.le] at this

end Bounds

/-! ## Adding an ancilla to the memory -/

section Anc

variable {A : Type} [Fintype A] [DecidableEq A]

theorem norm_dot_sq_le {X : Type} [Fintype X] (u v : X → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ nsq u * nsq v := by
  rw [← inner_toE, nsq, nsq, ← norm_toE_sq, ← norm_toE_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- A vector with the ancilla in `a₀`. -/
def liftVec (a₀ : A) (v : Qubits d.totalWires × N → ℂ) : Qubits d.totalWires × (N × A) → ℂ :=
  fun p => if p.2.2 = a₀ then v (p.1, p.2.1) else 0

/-- A turn, acting trivially on the ancilla. -/
noncomputable def liftM {k : ℕ} (V : Matrix (PS d k × N) (PS d k × N) ℂ) :
    Matrix (PS d k × (N × A)) (PS d k × (N × A)) ℂ :=
  (V ⊗ₖ (1 : Matrix A A ℂ)).submatrix (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm

theorem liftM_mem {k : ℕ} {V : Matrix (PS d k × N) (PS d k × N) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (PS d k × N) ℂ) :
    liftM (A := A) V ∈ Matrix.unitaryGroup (PS d k × (N × A)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (liftM V)ᴴ * liftM V = 1
  rw [liftM, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]
  change ((star V * V) ⊗ₖ (1 : Matrix A A ℂ)).submatrix _ _ = 1
  rw [Matrix.mem_unitaryGroup_iff'.mp hV, one_kronecker_one]
  exact submatrix_one_equiv _

omit [DecidableEq N] in
theorem nsq_liftVec (a₀ : A) (v : Qubits d.totalWires × N → ℂ) : nsq (liftVec a₀ v) = nsq v := by
  simp only [nsq, liftVec, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha; simp [ha]
  · simp

omit [DecidableEq N] in
theorem dot_liftVec (a₀ : A) (u v : Qubits d.totalWires × N → ℂ) :
    star (liftVec a₀ u) ⬝ᵥ liftVec a₀ v = star u ⬝ᵥ v := by
  simp only [dotProduct, liftVec, Fintype.sum_prod_type, Pi.star_apply]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha; simp [ha]
  · simp

theorem blockOp_liftVec (a₀ : A) (j : ℕ) (v : Qubits d.totalWires × N → ℂ) :
    blockOp d (N × A) j *ᵥ liftVec a₀ v = liftVec a₀ (blockOp d N j *ᵥ v) := by
  funext ⟨y, ν, a⟩
  simp only [blockOp, kronOne_mulVec_apply, liftVec]
  split_ifs with h
  · rfl
  · simp [mulVec, dotProduct]

omit [Fintype N] [DecidableEq N] [Fintype A] in
theorem turnOp_liftM {k : ℕ} (V : Matrix (PS d k × N) (PS d k × N) ℂ) :
    turnOp (liftM (A := A) V) = (turnOp V ⊗ₖ (1 : Matrix A A ℂ)).submatrix
      (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm := by
  ext ⟨y, ν, a⟩ ⟨y', ν', a'⟩
  simp only [turnOp, liftM, submatrix_apply, kroneckerMap_apply, Equiv.prodAssoc_symm_apply,
    gsplit_apply]
  ring

omit [DecidableEq N] in
theorem turnOp_liftVec (a₀ : A) {k : ℕ} (V : Matrix (PS d k × N) (PS d k × N) ℂ)
    (v : Qubits d.totalWires × N → ℂ) :
    turnOp (liftM (A := A) V) *ᵥ liftVec a₀ v = liftVec a₀ (turnOp V *ᵥ v) := by
  rw [turnOp_liftM, submatrix_mulVec_equiv]
  funext ⟨y, ν, a⟩
  simp only [Function.comp_apply, Equiv.prodAssoc_symm_apply, Equiv.symm_symm]
  rw [kronOne_mulVec_apply]
  have hf : (fun p => (liftVec a₀ v ∘ ⇑(Equiv.prodAssoc (Qubits d.totalWires) N A)) (p, a)) =
      if a = a₀ then v else 0 := by
    funext p
    simp only [Function.comp_apply, Equiv.prodAssoc_apply, liftVec]
    split_ifs <;> rfl
  rw [hf]
  simp only [liftVec]
  split_ifs
  · rfl
  · rw [mulVec_zero]; rfl

end Anc

/-! ## Stitching -/

section Stitch

omit [DecidableEq N] in
theorem turnOp_mul {k : ℕ} (A B : Matrix (PS d k × N) (PS d k × N) ℂ) :
    turnOp (A * B) = turnOp A * turnOp B := by
  rw [turnOp, turnOp, turnOp, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

theorem projQ_liftVec {A : Type} [Fintype A] [DecidableEq A] (a₀ : A)
    (Q : Qubits d.totalWires → Prop) [DecidablePred Q] (v : Qubits d.totalWires × N → ℂ) :
    projQ (N × A) Q *ᵥ liftVec a₀ v = liftVec a₀ (projQ N Q *ᵥ v) := by
  funext ⟨y, ν, a⟩
  rw [projQ_apply]
  simp only [liftVec, projQ_apply]
  split_ifs <;> rfl

variable (UB UF : Turns d N) {c : ℕ}

/-- The Uhlmann turn, as a turn at `c`. -/
noncomputable def uTurn (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ) (k : ℕ) :
    Matrix (PS d k × (N × KS d c)) (PS d k × (N × KS d c)) ℂ :=
  if h : k = c then by subst h; exact W.submatrix (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
  else 1

/-- **The stitched prover**: the prefix of `UB`, the Uhlmann turn, the suffix of `UF`. -/
noncomputable def stTurns (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ) :
    Turns d (N × KS d c) :=
  fun k => liftM (if k < c then UB k else UF k) * uTurn W k

theorem uTurn_mem {W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ}
    (hW : W ∈ Matrix.unitaryGroup _ ℂ) (k : ℕ) :
    uTurn (N := N) W k ∈ Matrix.unitaryGroup (PS d k × (N × KS d c)) ℂ := by
  unfold uTurn
  split_ifs with h
  · subst h
    rw [Matrix.mem_unitaryGroup_iff']
    change (W.submatrix _ _)ᴴ * W.submatrix _ _ = 1
    rw [conjTranspose_submatrix, submatrix_mul_equiv,
      show Wᴴ * W = 1 from Matrix.mem_unitaryGroup_iff'.mp hW]
    exact submatrix_one_equiv _
  · exact Submonoid.one_mem _

theorem stTurns_lt (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ) {k : ℕ}
    (hk : k < c) : stTurns UB UF W k = liftM (UB k) := by
  rw [stTurns, if_pos hk, uTurn, dif_neg (by omega), Matrix.mul_one]

theorem stTurns_gt (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ) {k : ℕ}
    (hk : c < k) : stTurns UB UF W k = liftM (UF k) := by
  rw [stTurns, if_neg (by omega), uTurn, dif_neg (by omega), Matrix.mul_one]

theorem stTurns_c (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ) :
    stTurns UB UF W c = liftM (UF c) * W.submatrix (Equiv.prodAssoc _ _ _).symm
      (Equiv.prodAssoc _ _ _).symm := by
  rw [stTurns, if_neg (lt_irrefl c), uTurn, dif_pos rfl]

theorem preOp_stTurns (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ)
    (a₀ : KS d c) (ξ₀ : Qubits d.totalWires × N → ℂ) :
    ∀ j ≤ c, preOp (stTurns UB UF W) j *ᵥ liftVec a₀ ξ₀ = liftVec a₀ (preOp UB j *ᵥ ξ₀)
  | 0, _ => blockOp_liftVec a₀ 0 ξ₀
  | j + 1, hj => by
    rw [preOp, preOp, ← mulVec_mulVec, ← mulVec_mulVec, preOp_stTurns W a₀ ξ₀ j (by omega),
      stTurns_lt UB UF W (by omega), turnOp_liftVec, blockOp_liftVec, mulVec_mulVec, mulVec_mulVec]

theorem sufOp_lift (a₀ : KS d c) (v : Qubits d.totalWires × N → ℂ) :
    ∀ j, sufOp (fun k => liftM (A := KS d c) (UF k)) c j *ᵥ liftVec a₀ v =
      liftVec a₀ (sufOp UF c j *ᵥ v)
  | 0 => by simp [sufOp]
  | j + 1 => by
    rw [sufOp, sufOp, ← mulVec_mulVec, ← mulVec_mulVec, sufOp_lift a₀ v j, turnOp_liftVec,
      blockOp_liftVec, mulVec_mulVec, mulVec_mulVec]

theorem sufOp_stTurns (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ) :
    ∀ j, sufOp (stTurns UB UF W) c (j + 1) =
      sufOp (fun k => liftM (A := KS d c) (UF k)) c (j + 1) *
        turnOp (W.submatrix (Equiv.prodAssoc (PS d c) N (KS d c)).symm (Equiv.prodAssoc _ _ _).symm)
  | 0 => by
    simp only [sufOp, Matrix.mul_one, Nat.add_zero]
    rw [stTurns_c, turnOp_mul, Matrix.mul_assoc]
  | j + 1 => by
    have ih := sufOp_stTurns W j
    rw [sufOp, ih, stTurns_gt UB UF W (by omega)]
    rw [show sufOp (fun k => liftM (A := KS d c) (UF k)) c (j + 1 + 1) =
      blockOp d _ (c + (j + 1) + 1) * turnOp (liftM (A := KS d c) (UF (c + (j + 1)))) *
        sufOp (fun k => liftM (A := KS d c) (UF k)) c (j + 1) from rfl]
    simp only [Matrix.mul_assoc]

omit [Fintype N] [DecidableEq N] in
theorem turnOp_uhl (W : Matrix ((PS d c × N) × KS d c) ((PS d c × N) × KS d c) ℂ) :
    turnOp (W.submatrix (Equiv.prodAssoc (PS d c) N (KS d c)).symm (Equiv.prodAssoc _ _ _).symm) =
      ((1 : Matrix (KS d c) (KS d c) ℂ) ⊗ₖ W).submatrix
        ((gsplit d c (N × KS d c)).trans ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _).symm))
        ((gsplit d c (N × KS d c)).trans ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _).symm)) := by
  ext p q
  simp only [turnOp, submatrix_apply, kroneckerMap_apply, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id]
  rfl

omit [Fintype N] [DecidableEq N] in
theorem liftVec_comp_symm (a₀ : KS d c) (v : Qubits d.totalWires × N → ℂ) :
    liftVec a₀ v ∘ ((gsplit d c (N × KS d c)).trans
      ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _).symm)).symm =
      addAnc a₀ (v ∘ (gsplit d c N).symm) := by
  funext ⟨h, ⟨p, ν⟩, a⟩
  simp only [Function.comp_apply, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, Prod.map_apply, id, Equiv.symm_symm, Equiv.prodAssoc_apply,
    gsplit_symm_apply, liftVec, addAnc]

/-- **Stitching.** A prefix reaching `ξB` and a suffix accepting `ξF` with certainty combine into a
generalized prover, so `F(ρ_B, ρ_F)² ≤ value d` on the wires kept at the cut. -/
theorem stitch (hd : d.Valid) (hc : c < d.numMsgs) (hB : ∀ k, UB k ∈ Matrix.unitaryGroup (PS d k × N) ℂ)
    (hF : ∀ k, UF k ∈ Matrix.unitaryGroup (PS d k × N) ℂ) (ξ₀ : Qubits d.totalWires × N → ℂ)
    (h₀ : GInit d ξ₀) (ξF : Qubits d.totalWires × N → ℂ) (hF1 : nsq ξF = 1)
    (hacc : projQ N (outBit d) *ᵥ (sufOp UF c (d.numMsgs - c) *ᵥ ξF) =
      sufOp UF c (d.numMsgs - c) *ᵥ ξF) :
    fidelity (margK N c (preOp UB c *ᵥ ξ₀)) (margK N c ξF) ^ 2 ≤ value d := by
  set ξB := preOp UB c *ᵥ ξ₀ with hξB
  have hN : Nonempty N := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [nsq] at hF1
  obtain ⟨ν₀⟩ := hN
  set a₀ : KS d c := fun _ => false
  obtain ⟨W, hW, hov⟩ := exists_unitary_overlap_eq_fidelity (margK_posSemidef c ξB)
    (margK_posSemidef c ξF) (rfl : IsPurification (ξB ∘ (gsplit d c N).symm) _)
    (rfl : IsPurification (ξF ∘ (gsplit d c N).symm) _) ((fun _ => false, ν₀) : PS d c × N) a₀
  set G' : GProver d := ⟨N × KS d c, stTurns UB UF W, fun k => Submonoid.mul_mem _
    (liftM_mem (by split_ifs; exact hB k; exact hF k)) (uTurn_mem hW k)⟩
  have hinit : GInit d (liftVec a₀ ξ₀) := by
    refine ⟨?_, fun y ν h => ?_⟩
    · have := nsq_liftVec a₀ ξ₀
      rw [nsq, Fintype.sum_prod_type] at this
      rw [this, nsq, Fintype.sum_prod_type]
      exact h₀.1
    · obtain ⟨ν, a⟩ := ν
      simp only [liftVec]
      split_ifs
      · exact h₀.2 y ν h
      · rfl
  obtain ⟨j, hj⟩ : ∃ j, d.numMsgs - c = j + 1 := ⟨d.numMsgs - c - 1, by omega⟩
  have hm : d.numMsgs = c + (j + 1) := by omega
  set Y := sufOp (fun k => liftM (A := KS d c) (UF k)) c (j + 1)
  have hY : Y ∈ Matrix.unitaryGroup _ ℂ := sufOp_mem _ (fun k => liftM_mem (hF k)) c _
  set x := turnOp (W.submatrix (Equiv.prodAssoc (PS d c) N (KS d c)).symm
    (Equiv.prodAssoc _ _ _).symm) *ᵥ liftVec a₀ ξB
  set z := liftVec a₀ ξF
  have hacc' : projQ (N × KS d c) (outBit d) *ᵥ (Y *ᵥ z) = Y *ᵥ z := by
    rw [sufOp_lift, projQ_liftVec, ← hj, hacc]
  have hz : nsq (Y *ᵥ z) = 1 := by rw [nsq_unitary hY, nsq_liftVec, hF1]
  have hdot : star z ⬝ᵥ x = (fidelity (margK N c ξB) (margK N c ξF) : ℂ) := by
    set e := (gsplit d c (N × KS d c)).trans ((Equiv.refl _).prodCongr
      (Equiv.prodAssoc (PS d c) N (KS d c)).symm) with he
    show star (liftVec a₀ ξF) ⬝ᵥ (turnOp (W.submatrix (Equiv.prodAssoc (PS d c) N (KS d c)).symm
      (Equiv.prodAssoc _ _ _).symm) *ᵥ liftVec a₀ ξB) = _
    rw [turnOp_uhl, submatrix_mulVec_equiv]
    have h := dot_comp_equiv e (liftVec a₀ ξF ∘ e.symm)
      (((1 : Matrix (KS d c) (KS d c) ℂ) ⊗ₖ W) *ᵥ (liftVec a₀ ξB ∘ e.symm))
    rw [show (liftVec a₀ ξF ∘ e.symm) ∘ e = liftVec a₀ ξF from by
      funext p; simp] at h
    rw [h, he, liftVec_comp_symm, liftVec_comp_symm, hov]
  have hrun : gAcc G' (liftVec a₀ ξ₀) = nsq (projQ (N × KS d c) (outBit d) *ᵥ (Y *ᵥ x)) := by
    rw [gAcc_eq_nsq]
    change nsq (projQ (N × KS d c) (outBit d) *ᵥ (preOp (stTurns UB UF W) d.numMsgs *ᵥ
      liftVec a₀ ξ₀)) = _
    rw [hm, preOp_add, ← mulVec_mulVec, preOp_stTurns UB UF W a₀ ξ₀ c le_rfl, sufOp_stTurns,
      ← mulVec_mulVec]
  have hcs := norm_dot_sq_le (projQ (N × KS d c) (outBit d) *ᵥ (Y *ᵥ z))
    (projQ (N × KS d c) (outBit d) *ᵥ (Y *ᵥ x))
  rw [hacc', hz, one_mul, dot_mulVec_adj, projQ_conjTranspose, hacc', dot_mulVec_adj,
    mulVec_mulVec, show Yᴴ * Y = 1 from Matrix.mem_unitaryGroup_iff'.mp hY, one_mulVec, hdot,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fidelity_nonneg _ _)] at hcs
  calc fidelity (margK N c ξB) (margK N c ξF) ^ 2 ≤ gAcc G' (liftVec a₀ ξ₀) := by rw [hrun]; exact hcs
    _ ≤ value d := gAcc_le_value G' _ hd hinit

end Stitch

/-! ## The cut bound -/

theorem nsq_projQ_le (Q : Qubits d.totalWires → Prop) [DecidablePred Q]
    (v : Qubits d.totalWires × N → ℂ) : nsq (projQ N Q *ᵥ v) ≤ nsq v := by
  rw [nsq_projQ, nsq, Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun ν _ => by
    split_ifs
    · exact le_rfl
    · positivity

/-- **The cut bound.** For any two unitary turn families and a unit cut state `ξ` after block
`c < m`, forward acceptance plus backward return is at most `1 + √(value d)`. -/
theorem cut_bound (hd : d.Valid) {c : ℕ} (hc : c < d.numMsgs) (UF UB : Turns d N)
    (hF : ∀ k, UF k ∈ Matrix.unitaryGroup (PS d k × N) ℂ)
    (hB : ∀ k, UB k ∈ Matrix.unitaryGroup (PS d k × N) ℂ)
    (ξ : Qubits d.totalWires × N → ℂ) (hξ : nsq ξ = 1) :
    fwdP UF c ξ + bwdP UB c ξ ≤ 1 + Real.sqrt (value d) := by
  have hv := Real.sqrt_nonneg (value d)
  have hfle : fwdP UF c ξ ≤ 1 := by
    unfold fwdP
    exact (nsq_projQ_le _ _).trans (by rw [nsq_unitary (sufOp_mem UF hF c _), hξ])
  have hble : bwdP UB c ξ ≤ 1 := by
    unfold bwdP
    exact (nsq_projQ_le _ _).trans (by
      rw [nsq_unitary (conjTranspose_mem_unitaryGroup (preOp_mem UB hB c)), hξ])
  by_cases hp : 0 < fwdP UF c ξ
  · by_cases hq : 0 < bwdP UB c ξ
    · obtain ⟨ξF, hF1, hacc, hfF⟩ := fwd_bound UF hF c ξ hp
      obtain ⟨ξ₀, h₀, hbB⟩ := bwd_bound UB hB c ξ hq
      have hst := stitch UB UF hd hc hB hF ξ₀ h₀ ξF hF1 hacc
      have hB1 : nsq (preOp UB c *ᵥ ξ₀) = 1 := by
        rw [nsq_unitary (preOp_mem UB hB c), nsq, Fintype.sum_prod_type]; exact h₀.1
      have h2 := fidelity_two_targets (isDensity_margK c hξ) (isDensity_margK c hF1)
        (isDensity_margK c hB1)
      have hsym : fidelity (margK N c ξF) (margK N c (preOp UB c *ᵥ ξ₀)) =
          fidelity (margK N c (preOp UB c *ᵥ ξ₀)) (margK N c ξF) :=
        fidelity_symm (margK_posSemidef c _) (margK_posSemidef c _)
      have hF' : fidelity (margK N c ξF) (margK N c (preOp UB c *ᵥ ξ₀)) ≤ Real.sqrt (value d) := by
        rw [hsym]
        exact Real.le_sqrt_of_sq_le hst
      linarith
    · push Not at hq
      linarith
  · push Not at hp
    linarith

end ShiQIP
