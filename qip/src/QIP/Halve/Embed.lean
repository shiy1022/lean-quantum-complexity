/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Halve.Desc

/-!
# Q31 — the d-picture of the halved description

A basis label of `halveDesc d n` splits into the working copy (a basis label of `d`), the control
wires (coin, output, control ancilla, zero-test ancillas) and the message wires. For a coin value
`b`, `Φ b v` embeds a vector `v` on the wires of `d` and the memory `N₀ × MB` (prover memory and
message wires) as the halved state with that coin and clean control wires.

* `runLayer_relabel_Φ`: a circuit of `d` on the working copy is the same circuit in the
  `d`-picture.
-/


namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

variable (d : Desc) (n : ℕ)

theorem hPriv_le_total : hPriv d ≤ (halveDesc d n).totalWires := by
  rw [totalWires_halveDesc]; exact hPriv_le_hOff d n _

theorem W_lt_total : d.totalWires + 3 ≤ (halveDesc d n).totalWires := by
  have := hPriv_le_total d n; unfold hPriv at this; omega

/-- The working copy inside the halved description. -/
def workEmb : Fin d.totalWires ↪ Fin (halveDesc d n).totalWires :=
  Fin.castLEEmb (by have := W_lt_total d n; omega)

/-- The coin wire. -/
def coinW : Fin (halveDesc d n).totalWires := ⟨hCoin d, by have := W_lt_total d n; unfold hCoin; omega⟩

/-- The output wire. -/
def outW : Fin (halveDesc d n).totalWires := ⟨hOut d, by have := W_lt_total d n; unfold hOut; omega⟩

/-- The control ancilla. -/
def caW : Fin (halveDesc d n).totalWires := ⟨hCa d, by have := W_lt_total d n; unfold hCa; omega⟩

/-- Message wires. -/
abbrev MB : Type := {w : Fin (halveDesc d n).totalWires // hPriv d ≤ (w : ℕ)} → Bool

variable {d n}

/-- The working-copy part of a basis label. -/
def workPart (y : Qubits (halveDesc d n).totalWires) : Qubits d.totalWires := fun x => y (workEmb d n x)

/-- The message part of a basis label. -/
def msgPart (y : Qubits (halveDesc d n).totalWires) : MB d n := fun w => y w.1

/-- Clean control wires, with the coin set to `b`. -/
def ctlOK (b : Bool) (y : Qubits (halveDesc d n).totalWires) : Prop :=
  y (coinW d n) = b ∧ y (outW d n) = false ∧ y (caW d n) = false ∧
    ∀ w : Fin (halveDesc d n).totalWires, d.totalWires + 3 ≤ (w : ℕ) → (w : ℕ) < hPriv d → y w = false

instance (b : Bool) : DecidablePred (ctlOK (d := d) (n := n) b) := fun _ => by
  unfold ctlOK; infer_instance

variable {N₀ : Type} [Fintype N₀] [DecidableEq N₀]

/-- **The embedding of the `d`-picture**, for the coin value `b`. -/
noncomputable def Φ (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) :
    Qubits (halveDesc d n).totalWires × N₀ → ℂ :=
  fun p => if ctlOK b p.1 then v (workPart p.1, (p.2, msgPart p.1)) else 0

/-! ## Circuits of `d` on the working copy -/

theorem mem_range_workEmb (w : Fin (halveDesc d n).totalWires) :
    w ∈ Set.range (workEmb d n) ↔ (w : ℕ) < d.totalWires := by
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨w, h⟩, rfl⟩

theorem slice_nonwork (y : Qubits (halveDesc d n).totalWires) (x : Qubits d.totalWires)
    (w : Fin (halveDesc d n).totalWires) (hw : d.totalWires ≤ (w : ℕ)) :
    (embSplit (workEmb d n)).symm (x, (embSplit (workEmb d n) y).2) w = y w := by
  have hw' : w ∉ Set.range (workEmb d n) := fun h => by
    rw [mem_range_workEmb] at h; omega
  exact (embSplit_symm_out (workEmb d n) x _ ⟨w, hw'⟩).trans rfl

theorem slice_work (y : Qubits (halveDesc d n).totalWires) (x : Qubits d.totalWires) :
    workPart ((embSplit (workEmb d n)).symm (x, (embSplit (workEmb d n) y).2)) = x :=
  funext fun i => embSplit_symm_emb (workEmb d n) x _ i

theorem slice_ctlOK (b : Bool) (y : Qubits (halveDesc d n).totalWires) (x : Qubits d.totalWires) :
    ctlOK b ((embSplit (workEmb d n)).symm (x, (embSplit (workEmb d n) y).2)) ↔ ctlOK b y := by
  have hc : d.totalWires ≤ ((coinW d n : Fin _) : ℕ) := by simp [coinW, hCoin]
  have ho : d.totalWires ≤ ((outW d n : Fin _) : ℕ) := by simp [outW, hOut]
  have ha : d.totalWires ≤ ((caW d n : Fin _) : ℕ) := by simp [caW, hCa]
  unfold ctlOK
  rw [slice_nonwork y x _ hc, slice_nonwork y x _ ho, slice_nonwork y x _ ha]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun w => forall_congr' fun h1 => forall_congr' fun _ => ?_)))
  rw [slice_nonwork y x w (by omega)]

theorem slice_msgPart (y : Qubits (halveDesc d n).totalWires) (x : Qubits d.totalWires) :
    msgPart ((embSplit (workEmb d n)).symm (x, (embSplit (workEmb d n) y).2)) = msgPart y := by
  funext w
  exact slice_nonwork y x w.1 (by have := w.2; unfold hPriv at this; omega)

/-- **A circuit of `d` on the working copy is the same circuit in the `d`-picture.** -/
theorem runLayer_work (l : List (Instr d.totalWires)) (b : Bool)
    (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    runLayer (l.map (instrMap (workEmb d n))) (fun y => Φ b v (y, μ)) =
      fun y => Φ b ((layerMat l ⊗ₖ (1 : Matrix (N₀ × MB d n) (N₀ × MB d n) ℂ)) *ᵥ v) (y, μ) := by
  funext y
  rw [runLayer_map_apply]
  have hs : sliceAt (workEmb d n) (fun y' => Φ b v (y', μ)) (embSplit (workEmb d n) y).2 =
      (if ctlOK b y then (1 : ℂ) else 0) • fun x => v (x, (μ, msgPart y)) := by
    funext x
    simp only [sliceAt, Φ, slice_ctlOK, slice_work, slice_msgPart, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hs, ← layerMat_mulVec, mulVec_smul, Φ, kronOne_mulVec_apply]
  change ((if ctlOK b y then (1 : ℂ) else 0) • (layerMat l *ᵥ fun x => v (x, (μ, msgPart y))))
    (workPart y) = _
  split_ifs <;> simp

/-! ## Controlled steps -/

section Ctrl

variable {M : ℕ}

/-- Flip one wire of a basis label. -/
def flipW (c : Fin M) (y : Bits M) : Bits M := Function.update y c (!y c)

theorem flipW_flipW (c : Fin M) (y : Bits M) : flipW c (flipW c y) = y := by
  funext w; simp only [flipW, Function.update_apply]; split_ifs with h <;> simp [h]

/-- A circuit avoiding `c` commutes with flipping `c`. -/
theorem runLayer_flip (c : Fin M) (l : List (Instr M)) (hl : ∀ g ∈ l, c ∉ g.support) (ψ : QState M) :
    runLayer l (fun y => ψ (flipW c y)) = fun y => runLayer l ψ (flipW c y) := by
  have key := runLayer_comp (fun w => w = c) (flipW c)
    (fun y i b hi => by
      funext w; simp only [flipW, Function.update_apply]
      split_ifs with h1 h2 h2 <;> simp_all)
    (fun y i hi => by simp only [flipW]; rw [Function.update_of_ne hi])
    (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl) l (fun g hg w hw h => hl g hg (h ▸ hw)) ψ
  simpa using key

theorem runLayer_x_apply (c : Fin M) (ψ : QState M) (y : Bits M) :
    runLayer [Instr.x c] ψ y = ψ (flipW c y) := by
  rw [runLayer_cons, runLayer_nil, apply_x]; rfl

/-- **Controlled on the coin being `0`.** -/
theorem runLayer_onF {c a : Fin M} (hca : c ≠ a) (l : List (Instr M))
    (hl : ∀ g ∈ l, c ∉ g.support ∧ a ∉ g.support) {ψ : QState M} (hψ : Clean a ψ) (y : Bits M) :
    runLayer ([Instr.x c] ++ ctrlInstrs c a l ++ [Instr.x c]) ψ y =
      if y c then ψ y else runLayer l ψ y := by
  rw [runLayer_append, runLayer_append, runLayer_x_apply]
  have hclean : Clean a (runLayer [Instr.x c] ψ) := by
    intro z hz
    rw [runLayer_x_apply]
    exact hψ _ (by simp only [flipW]; rw [Function.update_of_ne (Ne.symm hca)]; exact hz)
  rw [runLayer_ctrlInstrs hca l hl hclean]
  simp only [flipW, Function.update_self]
  cases hy : y c
  · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
    have := runLayer_flip c l (fun g hg => (hl g hg).1) ψ
    rw [show runLayer [Instr.x c] ψ = fun y => ψ (flipW c y) from funext (runLayer_x_apply c ψ)]
    rw [this]
    simp only [flipW]
    rw [show Function.update (Function.update y c true) c (!Function.update y c true c) = y by
      funext w; simp only [Function.update_apply]; split_ifs with h <;> simp [h, hy]]
  · rw [if_neg (by simp), if_pos rfl, runLayer_x_apply, show flipW c (Function.update y c !true) = y by
      funext w; simp only [flipW, Function.update_apply]; split_ifs with h <;> simp [h, hy]]

end Ctrl

section Swap

variable {M : ℕ}

/-- Swap the wire ranges `[p, p + r)` and `[q, q + r)` (when `q + r ≤ p` and `p + r ≤ M`). -/
def swR (p q r : ℕ) (w : Fin M) : Fin M :=
  if h : p ≤ w ∧ (w : ℕ) < p + r ∧ q + r ≤ p ∧ p + r ≤ M then ⟨q + (w - p), by omega⟩
  else if h' : q ≤ w ∧ (w : ℕ) < q + r ∧ q + r ≤ p ∧ p + r ≤ M then ⟨p + (w - q), by omega⟩
  else w

theorem val_swR (p q r : ℕ) (w : Fin M) : (swR p q r w : ℕ) =
    if p ≤ w ∧ (w : ℕ) < p + r ∧ q + r ≤ p ∧ p + r ≤ M then q + (w - p)
    else if q ≤ w ∧ (w : ℕ) < q + r ∧ q + r ≤ p ∧ p + r ≤ M then p + (w - q) else w := by
  unfold swR; split_ifs <;> rfl

/-- The gates swapping `[p, p + r)` with `[q, q + r)`. -/
def swapRange (p q r : ℕ) : List Gate := (List.range r).flatMap fun i => swapGates (p + i) (q + i)

theorem runLayer_swapRange (p q : ℕ) : ∀ r, q + r ≤ p → p + r ≤ M → ∀ ψ : QState M,
    runLayer ((swapRange p q r).filterMap (Gate.toInstr? M)) ψ = fun y => ψ (y ∘ swR p q r)
  | 0, _, _, ψ => by
    funext y
    simp only [swapRange, List.range_zero, List.flatMap_nil, List.filterMap_nil, runLayer_nil]
    congr 1
    funext w
    simp only [Function.comp_apply]
    congr 1
    apply Fin.ext; rw [val_swR]; split_ifs <;> omega
  | r + 1, h1, h2, ψ => by
    have ih := runLayer_swapRange p q r (by omega) (by omega) ψ
    have hne : (⟨p + r, by omega⟩ : Fin M) ≠ ⟨q + r, by omega⟩ := by
      intro e; simp only [Fin.mk.injEq] at e; omega
    rw [swapRange, List.range_succ, List.flatMap_append, List.filterMap_append, runLayer_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [show (p + r : ℕ) = ((⟨p + r, by omega⟩ : Fin M) : ℕ) from rfl,
      show (q + r : ℕ) = ((⟨q + r, by omega⟩ : Fin M) : ℕ) from rfl, filterMap_swapGates _ _ hne,
      runLayer_swapInstrs]
    rw [← swapRange, ih]
    funext y
    show ψ ((y ∘ ⇑(Equiv.swap _ _)) ∘ swR p q r) = _
    congr 1
    funext w
    simp only [Function.comp_apply]
    congr 1
    apply Fin.ext
    rw [Equiv.swap_apply_def]
    split_ifs with ha hb
    · simp only [Fin.ext_iff, val_swR] at ha ⊢; split_ifs at ha ⊢ <;> omega
    · simp only [Fin.ext_iff, val_swR] at hb ⊢; split_ifs at hb ⊢ <;> omega
    · simp only [Fin.ext_iff, val_swR] at ha hb ⊢; split_ifs at ha hb ⊢ <;> omega

end Swap

/-! ## Swaps between the working copy and the message wires -/

theorem msgOffset_add_width_le (e : Desc) (j : ℕ) : e.msgOffset j + e.msgWidth j ≤ e.totalWires := by
  simp only [Desc.msgOffset, Desc.msgWidth, Desc.totalWires]
  have h1 : ((e.msgs.take (j + 1)).map Message.width).sum =
      ((e.msgs.take j).map Message.width).sum + ((e.msgs[j]?).map Message.width).getD 0 := by
    rw [List.take_add_one, List.map_append, List.sum_append]
    cases e.msgs[j]? <;> simp
  have h2 : ((e.msgs.take (j + 1)).map Message.width).sum ≤ (e.msgs.map Message.width).sum := by
    conv_rhs => rw [← List.take_append_drop (j + 1) e.msgs]
    rw [List.map_append, List.sum_append]; omega
  omega

variable (d n) in
/-- The `d`-picture of the swap of `[p, p + r)` (message wires) with `[q, q + r)` (working copy). -/
def σSw (p q r : ℕ) (z : Qubits d.totalWires × (N₀ × MB d n)) : Qubits d.totalWires × (N₀ × MB d n) :=
  (fun w => if h : q ≤ (w : ℕ) ∧ (w : ℕ) < q + r ∧ hPriv d ≤ p ∧ p + r ≤ (halveDesc d n).totalWires then
      z.2.2 ⟨⟨p + (w - q), by omega⟩, by simp only; omega⟩ else z.1 w,
    (z.2.1, fun u => if h : p ≤ (u.1 : ℕ) ∧ (u.1 : ℕ) < p + r ∧ q + r ≤ d.totalWires then
      z.1 ⟨q + (u.1 - p), by omega⟩ else z.2.2 u))

theorem coinW_val : ((coinW d n : Fin _) : ℕ) = d.totalWires := rfl
theorem outW_val : ((outW d n : Fin _) : ℕ) = d.totalWires + 1 := rfl
theorem caW_val : ((caW d n : Fin _) : ℕ) = d.totalWires + 2 := rfl

omit [Fintype N₀] [DecidableEq N₀] in
/-- **A swap in the `d`-picture.** -/
theorem Φ_swR {p q r : ℕ} (hqr : q + r ≤ d.totalWires) (hp : hPriv d ≤ p)
    (hpr : p + r ≤ (halveDesc d n).totalWires) (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ)
    (y : Qubits (halveDesc d n).totalWires) (μ : N₀) :
    Φ b v (y ∘ swR p q r, μ) = Φ b (v ∘ σSw d n p q r) (y, μ) := by
  have hW : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have hfix : ∀ w : Fin (halveDesc d n).totalWires, d.totalWires ≤ (w : ℕ) → (w : ℕ) < hPriv d →
      swR p q r w = w := by
    intro w h1 h2; apply Fin.ext; rw [val_swR]; split_ifs <;> omega
  have hctl : ctlOK b (y ∘ swR p q r) ↔ ctlOK b y := by
    unfold ctlOK
    simp only [Function.comp_apply]
    rw [hfix _ (by rw [coinW_val]) (by rw [coinW_val]; omega),
      hfix _ (by rw [outW_val]; omega) (by rw [outW_val]; omega),
      hfix _ (by rw [caW_val]; omega) (by rw [caW_val]; omega)]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun w => forall_congr' fun h1 => forall_congr' fun h2 => ?_)))
    rw [hfix w (by omega) h2]
  simp only [Φ, Function.comp_apply]
  rw [if_congr hctl rfl rfl]
  split_ifs with hc
  · congr 1
    ext1
    · funext w
      simp only [workPart, σSw, Function.comp_apply]
      have hw := w.2
      split_ifs with h
      · congr 1; apply Fin.ext; rw [val_swR]; simp only [workEmb, Fin.castLEEmb_apply, Fin.val_castLE]
        split_ifs <;> omega
      · congr 1; apply Fin.ext; rw [val_swR]; simp only [workEmb, Fin.castLEEmb_apply, Fin.val_castLE]
        split_ifs <;> omega
    · ext1
      · rfl
      · funext u
        simp only [msgPart, σSw, Function.comp_apply]
        have hu := u.2
        split_ifs with h
        · congr 1; apply Fin.ext; rw [val_swR]; simp only [workEmb, Fin.castLEEmb_apply, Fin.val_castLE]
          split_ifs <;> omega
        · congr 1; apply Fin.ext; rw [val_swR]; split_ifs <;> omega
  · rfl


/-! ## Prover turns -/

section Turn

variable (d n) in
/-- The message wires outside register `k'`. -/
abbrev MBR (k : ℕ) : Type := {u : {w : Fin (halveDesc d n).totalWires // hPriv d ≤ (w : ℕ)} //
  ¬ inReg (halveDesc d n) k u.1} → Bool

theorem hPriv_le_of_inReg {k : ℕ} {w : Fin (halveDesc d n).totalWires} (h : inReg (halveDesc d n) k w) :
    hPriv d ≤ (w : ℕ) := inReg_ge_priv h

variable (d n) in
/-- Split the message wires at register `k'`. -/
def mbSplit (k : ℕ) : MB d n ≃ MBR d n k × Reg (halveDesc d n) k where
  toFun β := (fun u => β u.1, fun w => β ⟨w.1, hPriv_le_of_inReg w.2⟩)
  invFun p := fun u => if h : inReg (halveDesc d n) k u.1 then p.2 ⟨u.1, h⟩ else p.1 ⟨u, h⟩
  left_inv β := by funext u; simp only; split_ifs <;> rfl
  right_inv p := by
    obtain ⟨ρ, x⟩ := p
    ext u
    · simp only; rw [dif_neg u.2]
    · simp only; rw [dif_pos u.2]

variable (d n) in
/-- The memory reindexed for turn `k'`. -/
def memSplit (k : ℕ) : N₀ × MB d n ≃ MBR d n k × (Reg (halveDesc d n) k × N₀) where
  toFun p := ((mbSplit d n k p.2).1, ((mbSplit d n k p.2).2, p.1))
  invFun q := (q.2.2, (mbSplit d n k).symm (q.1, q.2.1))
  left_inv p := by simp
  right_inv q := by simp

variable (d n) in
/-- **A prover turn in the `d`-picture**: the matrix on prover memory and message wires. -/
noncomputable def PA (k : ℕ) (A : Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) :
    Matrix (N₀ × MB d n) (N₀ × MB d n) ℂ :=
  ((1 : Matrix (MBR d n k) (MBR d n k) ℂ) ⊗ₖ A).submatrix (memSplit d n k) (memSplit d n k)

theorem PA_mem {k : ℕ} {A : Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ}
    (hA : A ∈ Matrix.unitaryGroup _ ℂ) : PA d n k A ∈ Matrix.unitaryGroup (N₀ × MB d n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (PA d n k A)ᴴ * PA d n k A = 1
  rw [PA, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]
  change ((1 : Matrix (MBR d n k) (MBR d n k) ℂ) ⊗ₖ (star A * A)).submatrix _ _ = 1
  rw [Matrix.mem_unitaryGroup_iff'.mp hA, one_kronecker_one]
  exact submatrix_one_equiv _

omit [DecidableEq N₀] in
theorem PA_mulVec (k : ℕ) (A : Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ)
    (u : N₀ × MB d n → ℂ) (μ' : N₀) (β : MB d n) :
    (PA d n k A *ᵥ u) (μ', β) = ∑ x : Reg (halveDesc d n) k, ∑ μ : N₀,
      A ((mbSplit d n k β).2, μ') (x, μ) * u (μ, (mbSplit d n k).symm ((mbSplit d n k β).1, x)) := by
  rw [PA, submatrix_mulVec_equiv, Function.comp_apply]
  change (((1 : Matrix (MBR d n k) (MBR d n k) ℂ) ⊗ₖ A) *ᵥ _) ((mbSplit d n k β).1, ((mbSplit d n k β).2, μ')) = _
  rw [one_kron_mulVec_apply]
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Function.comp_apply]
  rfl

omit [DecidableEq N₀] in
/-- **A prover turn in the `d`-picture.** -/
theorem tv_Φ {k : ℕ} (A : Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (b : Bool)
    (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) :
    tv k A (Φ b v) = Φ b (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ PA d n k A) *ᵥ v) := by
  funext ⟨y, μ'⟩
  rw [tv_apply]
  have hW : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have hnr : ∀ w : Fin (halveDesc d n).totalWires, (w : ℕ) < hPriv d → ¬ inReg (halveDesc d n) k w :=
    fun w hw h => by have := hPriv_le_of_inReg h; omega
  have hset : ∀ (x : Reg (halveDesc d n) k) (w : Fin (halveDesc d n).totalWires), (w : ℕ) < hPriv d →
      PrefixData.regSet (halveDesc d n) k y x w = y w := fun x w hw => by
    rw [PrefixData.regSet_apply, dif_neg (hnr w hw)]
  have hctl : ∀ x, ctlOK b (PrefixData.regSet (halveDesc d n) k y x) ↔ ctlOK b y := by
    intro x
    unfold ctlOK
    rw [hset x _ (by rw [coinW_val]; omega), hset x _ (by rw [outW_val]; omega),
      hset x _ (by rw [caW_val]; omega)]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun w => forall_congr' fun h1 => forall_congr' fun h2 => ?_)))
    rw [hset x w h2]
  have hwork : ∀ x, workPart (PrefixData.regSet (halveDesc d n) k y x) = workPart y := fun x => by
    funext w; simp only [workPart]; exact hset x _ (by simp [workEmb]; omega)
  have hmsg : ∀ x, msgPart (PrefixData.regSet (halveDesc d n) k y x) =
      (mbSplit d n k).symm ((mbSplit d n k (msgPart y)).1, x) := fun x => by
    funext u; simp only [msgPart, mbSplit, Equiv.coe_fn_symm_mk, PrefixData.regSet_apply]
    split_ifs <;> rfl
  have hreg : (wireSplitE (halveDesc d n) k y).2 = (mbSplit d n k (msgPart y)).2 := rfl
  simp only [Φ, hctl, hwork, hmsg, hreg]
  split_ifs with hc
  · rw [one_kron_mulVec_apply, PA_mulVec]
  · simp

end Turn

end ShiQIP
