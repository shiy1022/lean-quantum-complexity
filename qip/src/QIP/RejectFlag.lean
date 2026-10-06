/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.ParallelRepeat

/-!
# Q26 — the reject flag and exact half acceptance

`rejectDesc d` adds a prover-controlled one-qubit flag to the last message of `d`, which goes
to the verifier, and accepts iff `d` accepts **and** the flag is `1`. The construction is the
paired description (`QIP.Pair`) of `d` with the *flag game* `flagDesc d`. The flag game has the
same schedule and widths `0`, except a one-qubit last message, which is copied into the output
wire.

* **Soundness**: `value_rejectDesc`: `value (rejectDesc d) = value d`. This holds against
  arbitrary provers, who may entangle the flag with everything else (Q25 product theorem).
* **Exact half acceptance**: `exists_accept_rejectDesc`: every `t ∈ [0, value d]` is the
  acceptance probability of some prover of `rejectDesc d`. In particular there is one with
  probability exactly `1/2` whenever `value d ≥ 1/2`. The honest prover plays an optimal
  strategy of `d` and an *independent* flag strategy that answers `1` with probability
  `t / value d`. The verifier never needs to know this probability.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Histories along inverse relabellings -/

section Relabel

variable {X Y X' Y' : ℕ → Type}
variable [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (X' i)] [∀ i, Fintype (Y' i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] [∀ i, DecidableEq (X' i)]
  [∀ i, DecidableEq (Y' i)]

theorem histMap_symm_apply (τX : ∀ i, X i ≃ X' i) (τY : ∀ i, Y i ≃ Y' i) :
    ∀ k (h : Hist X Y k),
      (histMap (fun i => (τX i).symm) (fun i => (τY i).symm) k).symm h = histMap τX τY k h
  | 0, _ => rfl
  | k + 1, ⟨⟨h, x⟩, y⟩ => by
    change ((((histMap (fun i => (τX i).symm) (fun i => (τY i).symm) k).symm h),
      ((τX k).symm).symm x), ((τY k).symm).symm y) = _
    rw [histMap_symm_apply τX τY k h]
    rfl

end Relabel

/-! ## Acceptance of product strategies -/

namespace PairData

variable {d₁ d₂ d : Desc} (D : PairData d₁ d₂ d)

include D in
/-- **Product strategies of a parallel composition multiply their acceptances.** For causal
strategies `Q₁`, `Q₂` of the two components (`d.numMsgs` turns), some prover of `d` accepts
with probability exactly the product of the two pairings. -/
theorem exists_accept_mul {Q₁ : ∀ k, Matrix (Hist (Reg d₁) (Reg d₁) k) (Hist (Reg d₁) (Reg d₁) k) ℂ}
    {Q₂ : ∀ k, Matrix (Hist (Reg d₂) (Reg d₂) k) (Hist (Reg d₂) (Reg d₂) k) ℂ}
    (h₁ : IsStrategy d.numMsgs Q₁) (h₂ : IsStrategy d.numMsgs Q₂) :
    ∃ P : Prover d, accept P =
      (trace (testerAt d₁ d.numMsgs * Q₁ d.numMsgs)).re *
        (trace (testerAt d₂ d.numMsgs * Q₂ d.numMsgs)).re := by
  set τ' : ∀ i, Reg d₁ i × Reg d₂ i ≃ Reg d i := fun i => (D.τ i).symm
  have hQ := isStrategy_relabel τ' τ' (isStrategy_prod h₁ h₂)
  obtain ⟨P, -, hP⟩ := exists_opStrategy_of_isStrategy hQ
  refine ⟨P, ?_⟩
  rw [accept_eq_pairing, hP _ le_rfl, D.tester_eq]
  have hm : ∀ h : Hist (Reg d) (Reg d) d.numMsgs,
      (histMap τ' τ' d.numMsgs).symm h = histMap D.τ D.τ d.numMsgs h := by
    intro h
    exact histMap_symm_apply D.τ D.τ d.numMsgs h
  have e : relabel τ' τ' (fun k => prodMat (Q₁ k) (Q₂ k)) d.numMsgs =
      (prodMat (Q₁ d.numMsgs) (Q₂ d.numMsgs)).submatrix (histMap D.τ D.τ d.numMsgs)
        (histMap D.τ D.τ d.numMsgs) := by
    ext a b
    simp only [relabel, submatrix_apply, hm]
  rw [e, submatrix_mul_equiv, trace_submatrix_equiv, trace_prodMat_mul,
    re_mul_of_nonneg (psd_trace_mul_nonneg (testerAt_posSemidef _ _) (h₁.posSemidef _ le_rfl))]

end PairData

/-! ## Non-adaptive strategies -/

section NonAdaptive

variable {X Y : ℕ → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
variable [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]

/-- The strategy that ignores its inputs and answers turn `k` with the state `σ k`. -/
def nonAdaptive (σ : ∀ k, Matrix (Y k) (Y k) ℂ) : ∀ k, Matrix (Hist X Y k) (Hist X Y k) ℂ
  | 0 => 1
  | k + 1 => (nonAdaptive σ k ⊗ₖ (1 : Matrix (X k) (X k) ℂ)) ⊗ₖ σ k

theorem nonAdaptive_posSemidef {σ : ∀ k, Matrix (Y k) (Y k) ℂ} (hσ : ∀ k, IsDensity (σ k)) :
    ∀ k, (nonAdaptive (X := X) σ k).PosSemidef
  | 0 => PosSemidef.one
  | k + 1 => ((nonAdaptive_posSemidef hσ k).kronecker PosSemidef.one).kronecker (hσ k).posSemidef

theorem nonAdaptive_isStrategy {σ : ∀ k, Matrix (Y k) (Y k) ℂ} (hσ : ∀ k, IsDensity (σ k))
    (r : ℕ) : IsStrategy r (nonAdaptive (X := X) σ) where
  zero := rfl
  posSemidef k _ := nonAdaptive_posSemidef hσ k
  causal k _ := by
    unfold Causal
    change traceRight ((nonAdaptive σ k ⊗ₖ (1 : Matrix (X k) (X k) ℂ)) ⊗ₖ σ k) = _
    rw [traceRight_kronecker, (hσ k).trace_eq_one, one_smul]

end NonAdaptive

/-! ## The flag game -/

/-- Widths of the flag game: all `0` except the last message, of width `1`. -/
def flagWidths (m : ℕ) : List ℕ := List.replicate (m - 1) 0 ++ [1]

/-- Messages of the flag game: the directions of `ms`, the flag widths. -/
def flagMsgs (ms : List Message) : List Message :=
  List.zipWith (fun msg w => ⟨msg.dir, w⟩) ms (flagWidths ms.length)

/-- **The flag game** for the schedule of `d`: the last message carries one qubit, which the
final block copies into the output wire `0`. -/
def flagDesc (d : Desc) : Desc where
  priv := 1
  out := 0
  msgs := flagMsgs d.msgs
  blocks := (List.range (d.numMsgs + 1)).map fun j => if j = d.numMsgs then [Gate.cnot 1 0] else []

section Flag

variable {d : Desc} (hm : 1 ≤ d.numMsgs)

theorem length_flagWidths (hm : 1 ≤ d.numMsgs) : (flagWidths d.numMsgs).length = d.numMsgs := by
  simp [flagWidths]; omega

theorem zipWith_widths : ∀ (ms : List Message) (ws : List ℕ), ms.length = ws.length →
    (List.zipWith (fun msg w => (⟨msg.dir, w⟩ : Message)) ms ws).map Message.width = ws
  | [], [], _ => rfl
  | m :: ms, w :: ws, h => by
    simp only [List.zipWith_cons_cons, List.map_cons, zipWith_widths ms ws (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem zipWith_dirs : ∀ (ms : List Message) (ws : List ℕ), ms.length = ws.length →
    (List.zipWith (fun msg w => (⟨msg.dir, w⟩ : Message)) ms ws).map Message.dir =
      ms.map Message.dir
  | [], [], _ => rfl
  | m :: ms, w :: ws, h => by
    simp only [List.zipWith_cons_cons, List.map_cons, zipWith_dirs ms ws (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem flagMsgs_widths (hm : 1 ≤ d.numMsgs) :
    (flagMsgs d.msgs).map Message.width = flagWidths d.numMsgs :=
  zipWith_widths _ _ (length_flagWidths hm).symm

theorem flagMsgs_dirs (hm : 1 ≤ d.numMsgs) :
    (flagMsgs d.msgs).map Message.dir = d.msgs.map Message.dir :=
  zipWith_dirs _ _ (length_flagWidths hm).symm

theorem numMsgs_flagDesc (hm : 1 ≤ d.numMsgs) : (flagDesc d).numMsgs = d.numMsgs := by
  have := congrArg List.length (flagMsgs_widths hm)
  rw [List.length_map, length_flagWidths hm] at this
  exact this

theorem totalWires_flagDesc (hm : 1 ≤ d.numMsgs) : (flagDesc d).totalWires = 2 := by
  simp [Desc.totalWires, flagDesc, flagMsgs_widths hm, flagWidths]

theorem psum_flagWidths {j : ℕ} (hj : j + 1 ≤ d.numMsgs) : psum (flagWidths d.numMsgs) j = 0 := by
  simp only [psum, flagWidths]
  rw [List.take_append_of_le_length (by simp; omega)]
  simp

theorem getD_flagWidths (hm : 1 ≤ d.numMsgs) (j : ℕ) :
    (flagWidths d.numMsgs).getD j 0 = if j + 1 = d.numMsgs then 1 else 0 := by
  simp only [flagWidths, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge j (d.numMsgs - 1) with hj | hj
  · rw [List.getElem?_append_left (by simpa using hj), List.getElem?_replicate, if_pos hj,
      if_neg (by omega)]
    rfl
  · rw [List.getElem?_append_right (by simpa using hj)]
    simp only [List.length_replicate]
    obtain ⟨t, rfl⟩ : ∃ t, j = d.numMsgs - 1 + t := ⟨j - (d.numMsgs - 1), by omega⟩
    rw [show d.numMsgs - 1 + t - (d.numMsgs - 1) = t by omega]
    cases t with
    | zero => rw [if_pos (by omega)]; rfl
    | succ t => rw [if_neg (by omega)]; simp

/-- **Message registers of the flag game**: only the last one, wire `1`. -/
theorem inReg_flagDesc (hm : 1 ≤ d.numMsgs) (j : ℕ) (w : Fin (flagDesc d).totalWires) :
    inReg (flagDesc d) j w ↔ j + 1 = d.numMsgs ∧ (w : ℕ) = 1 := by
  unfold inReg
  rw [msgOffset_eq, msgWidth_eq]
  simp only [segs, psum_cons_succ, List.getD_cons_succ, flagDesc, flagMsgs_widths hm,
    getD_flagWidths hm]
  by_cases hj : j + 1 = d.numMsgs
  · rw [psum_flagWidths hj.le]; simp only [if_pos hj]; omega
  · simp only [if_neg hj]; omega

end Flag

/-! ## Wires and registers of the flag game -/

section FlagWires

variable {d : Desc}

/-- The output wire `0` of the flag game. -/
def oW (hm : 1 ≤ d.numMsgs) : Fin (flagDesc d).totalWires :=
  ⟨0, by rw [totalWires_flagDesc hm]; omega⟩

/-- The flag wire `1` of the flag game. -/
def fW (hm : 1 ≤ d.numMsgs) : Fin (flagDesc d).totalWires :=
  ⟨1, by rw [totalWires_flagDesc hm]; omega⟩

theorem oW_ne_fW (hm : 1 ≤ d.numMsgs) : oW hm ≠ fW hm := fun h => by
  simpa [oW, fW] using congrArg Fin.val h

theorem fin_flag (hm : 1 ≤ d.numMsgs) (v : Fin (flagDesc d).totalWires) :
    v = oW hm ∨ v = fW hm := by
  have hv : (v : ℕ) < 2 := totalWires_flagDesc hm ▸ v.2
  rcases v with ⟨v, hv'⟩
  rcases (show v = 0 ∨ v = 1 by simp at hv; omega) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem qubits_flag_ext (hm : 1 ≤ d.numMsgs) {w w' : Qubits (flagDesc d).totalWires}
    (h0 : w (oW hm) = w' (oW hm)) (h1 : w (fW hm) = w' (fW hm)) : w = w' :=
  funext fun v => by rcases fin_flag hm v with rfl | rfl <;> assumption

theorem not_inReg_oW (hm : 1 ≤ d.numMsgs) (j : ℕ) : ¬ inReg (flagDesc d) j (oW hm) := by
  rw [inReg_flagDesc hm]; simp [oW]

theorem isEmpty_reg_flag (hm : 1 ≤ d.numMsgs) {j : ℕ} (hj : j + 1 ≠ d.numMsgs) :
    IsEmpty {w // inReg (flagDesc d) j w} :=
  ⟨fun ⟨w, hw⟩ => hj ((inReg_flagDesc hm j w).mp hw).1⟩

theorem subsingleton_reg_flag (hm : 1 ≤ d.numMsgs) {j : ℕ} (hj : j + 1 ≠ d.numMsgs) :
    Subsingleton (Reg (flagDesc d) j) := by
  have := isEmpty_reg_flag hm hj
  exact ⟨fun a b => funext fun s => isEmptyElim s⟩

/-- The flag position inside the last register. -/
def fSub (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs) :
    {w // inReg (flagDesc d) n w} := ⟨fW hm, (inReg_flagDesc hm n _).mpr ⟨hn, rfl⟩⟩

theorem eq_fSub (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs)
    (s : {w // inReg (flagDesc d) n w}) : s = fSub hm hn := by
  apply Subtype.ext
  rcases fin_flag hm s.1 with h | h
  · exact absurd (h ▸ s.2) (not_inReg_oW hm n)
  · exact h

theorem reg_flag_ext (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs)
    {r r' : Reg (flagDesc d) n} (h : r (fSub hm hn) = r' (fSub hm hn)) : r = r' :=
  funext fun s => by rw [eq_fSub hm hn s]; exact h

end FlagWires

/-! ## The tester of the flag game -/

section FlagTester

variable {d : Desc}

theorem blocks_flag_getD {j : ℕ} (hj : j < d.numMsgs) : (flagDesc d).blocks.getD j [] = [] := by
  simp [flagDesc, List.getD_eq_getElem?_getD, hj.ne, Nat.lt_succ_of_lt hj]

theorem blockMat_flag_lt {j : ℕ} (hj : j < d.numMsgs) : blockMat (flagDesc d) j = 1 := by
  rw [blockMat, blocks_flag_getD hj]; rfl

theorem blockMat_flag_last (hm : 1 ≤ d.numMsgs) :
    blockMat (flagDesc d) d.numMsgs = cnotMat (fW hm) (oW hm) (oW_ne_fW hm).symm := by
  have hg : ((flagDesc d).blocks.getD d.numMsgs []).filterMap
      (Gate.toInstr? (flagDesc d).totalWires) = [ShiShallow.Instr.cnot (fW hm) (oW hm)
        (oW_ne_fW hm).symm] := by
    have hb : (flagDesc d).blocks.getD d.numMsgs [] = [Gate.cnot 1 0] := by
      simp [flagDesc, List.getD_eq_getElem?_getD]
    rw [hb]
    simp [Gate.toInstr?, totalWires_flagDesc hm, fW, oW]
  rw [blockMat, hg, layerMat_cons]
  simp [layerMat, instrMat]

/-- **Before the last block, the flag game only carries `|0⟩`.** -/
theorem transMat_flag : ∀ j < d.numMsgs,
    transMat (flagDesc d) j = Matrix.of fun w _ => zeroVec _ w
  | 0, h => by
    ext w u
    simp [transMat, blockMat_flag_lt h]
  | j + 1, h => by
    have hm : 1 ≤ d.numMsgs := by omega
    ext w ⟨⟨u, x⟩, y⟩
    change (blockMat (flagDesc d) (j + 1) * transfer (wireSplitE (flagDesc d) j)
      (transMat (flagDesc d) j)) w ((u, x), y) = _
    rw [blockMat_flag_lt h, Matrix.one_mul, transMat_flag j (by omega)]
    have hs := subsingleton_reg_flag hm (j := j) (by omega)
    simp only [transfer, of_apply]
    rw [if_pos (Subsingleton.elim _ _)]
    have : ((wireSplitE (flagDesc d) j w).1, x) = wireSplitE (flagDesc d) j w :=
      Prod.ext rfl (Subsingleton.elim _ _)
    rw [this, Equiv.symm_apply_apply]
    rfl

theorem cnotMat_mul_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) {H : Type}
    (T : Matrix (Qubits n) H ℂ) (w : Qubits n) (h : H) :
    (cnotMat i j hij * T) w h = T (cnotFun i j w) h := by
  have := congrFun (cnotMat_mulVec i j hij (fun v => T v h)) w
  simpa [mulVec, dotProduct, mul_apply, ShiShallow.cnotState, cnotFun] using this

/-- **The last transition matrix of the flag game.** -/
theorem transMat_flag_last (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs)
    (w : Qubits (flagDesc d).totalWires) (u : Hist (Reg (flagDesc d)) (Reg (flagDesc d)) n)
    (x y : Reg (flagDesc d) n) :
    transMat (flagDesc d) (n + 1) w ((u, x), y) =
      if w (fW hm) = y (fSub hm hn) ∧ w (oW hm) = w (fW hm) ∧ x (fSub hm hn) = false
      then 1 else 0 := by
  change (blockMat (flagDesc d) (n + 1) * transfer (wireSplitE (flagDesc d) n)
    (transMat (flagDesc d) n)) w ((u, x), y) = _
  have hb : blockMat (flagDesc d) (n + 1) = cnotMat (fW hm) (oW hm) (oW_ne_fW hm).symm := by
    rw [hn]; exact blockMat_flag_last hm
  rw [hb, cnotMat_mul_apply, transMat_flag n (by omega)]
  set v := cnotFun (fW hm) (oW hm) w
  have hvo : v (oW hm) = xor (w (oW hm)) (w (fW hm)) := by
    simp [v, cnotFun]
  have hvf : v (fW hm) = w (fW hm) := by
    simp [v, cnotFun, Function.update_of_ne (oW_ne_fW hm).symm]
  simp only [transfer, of_apply, zeroVec]
  have hread : (wireSplitE (flagDesc d) n v).2 = y ↔ v (fW hm) = y (fSub hm hn) :=
    ⟨fun h => by rw [← h]; rfl, fun h => reg_flag_ext hm hn h⟩
  have hzero : (wireSplitE (flagDesc d) n).symm ((wireSplitE (flagDesc d) n v).1, x) =
      Qubits.zero _ ↔ v (oW hm) = false ∧ x (fSub hm hn) = false := by
    constructor
    · intro h
      have h0 := congrFun h (oW hm)
      have h1 := congrFun h (fW hm)
      rw [wireSplitE_symm_apply, dif_neg (not_inReg_oW hm n)] at h0
      rw [wireSplitE_symm_apply, dif_pos ((inReg_flagDesc hm n (fW hm)).mpr ⟨hn, rfl⟩)] at h1
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      apply qubits_flag_ext hm
      · rw [wireSplitE_symm_apply, dif_neg (not_inReg_oW hm n)]; exact h0
      · rw [wireSplitE_symm_apply, dif_pos ((inReg_flagDesc hm n (fW hm)).mpr ⟨hn, rfl⟩)]; exact h1
  by_cases h1 : v (fW hm) = y (fSub hm hn)
  · rw [if_pos (hread.mpr h1)]
    by_cases h2 : v (oW hm) = false ∧ x (fSub hm hn) = false
    · rw [if_pos (hzero.mpr h2), if_pos]
      refine ⟨hvf ▸ h1, ?_, h2.2⟩
      have := h2.1; rw [hvo] at this
      cases hw0 : w (oW hm) <;> cases hw1 : w (fW hm) <;> simp_all
    · rw [if_neg (fun e => h2 (hzero.mp e)), if_neg]
      rintro ⟨-, h3, h4⟩
      exact h2 ⟨by rw [hvo, h3]; simp, h4⟩
  · rw [if_neg (fun e => h1 (hread.mp e)), if_neg]
    rintro ⟨h3, -, -⟩
    exact h1 (hvf ▸ h3)

end FlagTester

/-! ## The flag pairing -/

section FlagPairing

variable {d : Desc}

theorem subsingleton_hist_flag (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs) :
    ∀ k ≤ n, Subsingleton (Hist (Reg (flagDesc d)) (Reg (flagDesc d)) k)
  | 0, _ => inferInstanceAs (Subsingleton Unit)
  | k + 1, hk => by
    have h1 := subsingleton_hist_flag hm hn k (by omega)
    have h2 := subsingleton_reg_flag hm (j := k) (by omega)
    exact inferInstanceAs (Subsingleton ((Hist _ _ k × Reg (flagDesc d) k) × Reg (flagDesc d) k))

/-- Some history of the flag game (all registers `0`). -/
def histZero (d : Desc) : ∀ k, Hist (Reg d) (Reg d) k
  | 0 => ()
  | k + 1 => (((histZero d k : Hist (Reg d) (Reg d) k), fun _ => false), fun _ => false)

/-- The accepted history: last input `0`, last answer `1`. -/
def hAcc (d : Desc) (n : ℕ) : Hist (Reg (flagDesc d)) (Reg (flagDesc d)) (n + 1) :=
  ((histZero (flagDesc d) n, fun _ => false), fun _ => true)

/-- The last input register of a history. -/
def lastIn {n : ℕ} (H : Hist (Reg (flagDesc d)) (Reg (flagDesc d)) (n + 1)) : Reg (flagDesc d) n :=
  (H : (Hist (Reg (flagDesc d)) (Reg (flagDesc d)) n × Reg (flagDesc d) n) × Reg (flagDesc d) n).1.2

/-- The last output register of a history. -/
def lastOut {n : ℕ} (H : Hist (Reg (flagDesc d)) (Reg (flagDesc d)) (n + 1)) : Reg (flagDesc d) n :=
  (H : (Hist (Reg (flagDesc d)) (Reg (flagDesc d)) n × Reg (flagDesc d) n) × Reg (flagDesc d) n).2

/-- **The tester of the flag game is the matrix unit at the accepted history.** -/
theorem testerAt_flag (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs) :
    testerAt (flagDesc d) (n + 1) = Matrix.single (hAcc d n) (hAcc d n) 1 := by
  have hsub := subsingleton_hist_flag hm hn n le_rfl
  set w₁ : Qubits (flagDesc d).totalWires := fun _ => true
  have hout : ∀ w : Qubits (flagDesc d).totalWires, outBit (flagDesc d) w ↔ w (oW hm) = true :=
    fun w => ⟨fun ⟨_, h⟩ => h, fun h => ⟨(oW hm).2, h⟩⟩
  have hgood : ∀ H : Hist (Reg (flagDesc d)) (Reg (flagDesc d)) (n + 1),
      H = hAcc d n ↔ lastOut H (fSub hm hn) = true ∧ lastIn H (fSub hm hn) = false := by
    rintro ⟨⟨u, x⟩, y⟩
    constructor
    · intro h; rw [h]; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext (Prod.ext (Subsingleton.elim _ _) (reg_flag_ext hm hn h2))
        (reg_flag_ext hm hn h1)
  have hA : ∀ w (H : Hist (Reg (flagDesc d)) (Reg (flagDesc d)) (n + 1)),
      transMat (flagDesc d) (n + 1) w H = if w (fW hm) = lastOut H (fSub hm hn) ∧
        w (oW hm) = w (fW hm) ∧ lastIn H (fSub hm hn) = false then 1 else 0 := by
    intro w H
    obtain ⟨⟨u, x⟩, y⟩ := H
    exact transMat_flag_last hm hn w u x y
  have hA₁ : ∀ H, transMat (flagDesc d) (n + 1) w₁ H = if H = hAcc d n then 1 else 0 := by
    intro H
    rw [hA]
    by_cases hH : H = hAcc d n
    · rw [if_pos hH, if_pos]
      obtain ⟨h1, h2⟩ := (hgood H).mp hH
      exact ⟨h1.symm, rfl, h2⟩
    · rw [if_neg hH, if_neg]
      rintro ⟨h1, -, h2⟩
      exact hH ((hgood H).mpr ⟨h1.symm, h2⟩)
  ext H H'
  rw [testerAt, mul_apply]
  simp only [basisEffect, mul_diagonal, conjTranspose_apply]
  rw [Finset.sum_eq_single w₁]
  · rw [hA₁, hA₁, if_pos ((hout w₁).mpr rfl), single_apply]
    by_cases a : H = hAcc d n <;> by_cases b : H' = hAcc d n
    · simp [a, b]
    · simp [a, b, Ne.symm b]
    · simp [a, Ne.symm a]
    · simp [a, Ne.symm a]
  · intro w _ hw
    by_cases h0 : w (oW hm) = true
    · have h1 : w (fW hm) = false := by
        by_contra h1
        exact hw (qubits_flag_ext hm (by simp [w₁, h0]) (by simpa [w₁] using h1))
      have hz : transMat (flagDesc d) (n + 1) w H' = 0 := by
        rw [hA, if_neg]
        intro h
        have h2 := h.2.1
        rw [h0, h1] at h2
        exact Bool.noConfusion h2
      rw [hz, mul_zero]
    · rw [if_neg (fun h => h0 ((hout w).mp h))]; simp
  · simp

theorem pairing_flag (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs)
    (Q : Matrix (Hist (Reg (flagDesc d)) (Reg (flagDesc d)) (n + 1))
      (Hist (Reg (flagDesc d)) (Reg (flagDesc d)) (n + 1)) ℂ) :
    trace (testerAt (flagDesc d) (n + 1) * Q) = Q (hAcc d n) (hAcc d n) := by
  rw [testerAt_flag hm hn, trace_single_mul, one_smul]

end FlagPairing

/-! ## Flag strategies and the flag value -/

section FlagValue

variable {d : Desc}

/-- Answer "all zeros" with probability `1 - q` and "all ones" with probability `q`. -/
noncomputable def flagSigma (d : Desc) (q : ℝ) (k : ℕ) :
    Matrix (Reg (flagDesc d) k) (Reg (flagDesc d) k) ℂ :=
  diagonal fun r => (if r = (fun _ => false) then ((1 - q : ℝ) : ℂ) else 0) +
    (if r = (fun _ => true) then ((q : ℝ) : ℂ) else 0)

theorem flagSigma_isDensity {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    IsDensity (flagSigma d q k) := by
  constructor
  · refine PosSemidef.diagonal fun r => ?_
    refine add_nonneg ?_ ?_
    · split_ifs
      · exact Complex.zero_le_real.mpr (by linarith)
      · exact le_rfl
    · split_ifs
      · exact Complex.zero_le_real.mpr hq0
      · exact le_rfl
  · simp only [flagSigma, trace_diagonal, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    push_cast; ring

theorem nonAdaptive_flag_zero (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs) (q : ℝ) :
    ∀ k ≤ n, nonAdaptive (X := Reg (flagDesc d)) (flagSigma d q) k (histZero _ k)
      (histZero _ k) = 1
  | 0, _ => rfl
  | k + 1, hk => by
    have hs := subsingleton_reg_flag hm (j := k) (by omega)
    change (nonAdaptive (X := Reg (flagDesc d)) (flagSigma d q) k (histZero _ k) (histZero _ k) *
      (1 : Matrix (Reg (flagDesc d) k) (Reg (flagDesc d) k) ℂ) (fun _ => false) (fun _ => false)) *
        flagSigma d q k (fun _ => false) (fun _ => false) = 1
    rw [nonAdaptive_flag_zero hm hn q k (by omega), one_apply_eq, one_mul, one_mul, flagSigma,
      diagonal_apply_eq, if_pos rfl, if_pos (Subsingleton.elim _ _)]
    push_cast; ring

/-- **The flag pairing of a flag strategy is its answering probability.** -/
theorem pairing_flagSigma (hm : 1 ≤ d.numMsgs) {n : ℕ} (hn : n + 1 = d.numMsgs) (q : ℝ) :
    (trace (testerAt (flagDesc d) (n + 1) *
      nonAdaptive (X := Reg (flagDesc d)) (flagSigma d q) (n + 1))).re = q := by
  rw [pairing_flag hm hn]
  change ((nonAdaptive (X := Reg (flagDesc d)) (flagSigma d q) n (histZero _ n) (histZero _ n) *
    (1 : Matrix (Reg (flagDesc d) n) (Reg (flagDesc d) n) ℂ) (fun _ => false) (fun _ => false)) *
      flagSigma d q n (fun _ => true) (fun _ => true)).re = q
  have hne : (fun _ => true : Reg (flagDesc d) n) ≠ fun _ => false := fun h => by
    have := congrFun h (fSub hm hn); simp at this
  rw [nonAdaptive_flag_zero hm hn q n le_rfl, one_apply_eq, one_mul, one_mul, flagSigma,
    diagonal_apply_eq, if_neg hne, if_pos rfl, zero_add, Complex.ofReal_re]

/-- **The flag game has value one.** -/
theorem value_flagDesc (hm : 1 ≤ d.numMsgs) : value (flagDesc d) = 1 := by
  obtain ⟨n, hn⟩ : ∃ n, n + 1 = d.numMsgs := ⟨d.numMsgs - 1, by omega⟩
  have hk : (flagDesc d).numMsgs = n + 1 := (numMsgs_flagDesc hm).trans hn.symm
  refine le_antisymm (value_mem_Icc _).2 ?_
  rw [value_eq_sdpVal_testerAt _ hk]
  have h := pairing_le_sdpVal (testerAt_posSemidef _ _)
    (nonAdaptive_isStrategy (X := Reg (flagDesc d)) (flagSigma_isDensity (d := d) zero_le_one le_rfl)
      (n + 1))
  rwa [pairing_flagSigma hm hn] at h

end FlagValue

/-! ## Validity of the flag game -/

/-- The last message goes to the verifier. -/
def LastToVerifier (d : Desc) : Prop :=
  (d.msgs.map Message.dir).getD (d.numMsgs - 1) .toVerifier = .toVerifier

theorem flagDesc_valid {d : Desc} (hd : d.Valid) (hm : 1 ≤ d.numMsgs)
    (hlast : LastToVerifier d) : (flagDesc d).Valid := by
  unfold Desc.Valid Desc.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by simp [flagDesc], ?_⟩, ?_⟩, ?_⟩
  · change Desc.alternates (flagMsgs d.msgs) = true
    rw [alternates_congr _ d.msgs (flagMsgs_dirs hm)]
    exact hd.alternates
  · have := numMsgs_flagDesc hm
    simp only [Desc.numMsgs] at this
    simp only [flagDesc, List.length_map, List.length_range]
    exact congrArg (· + 1) this.symm
  · refine blocksOkFrom_of _ 0 fun i g hg => ?_
    rw [zero_add]
    by_cases hi : i < d.numMsgs
    · rw [blocks_flag_getD hi] at hg; simp at hg
    · by_cases hi' : i = d.numMsgs
      · subst hi'
        have hb : (flagDesc d).blocks.getD d.numMsgs [] = [Gate.cnot 1 0] := by
          simp [flagDesc, List.getD_eq_getElem?_getD]
        rw [hb, List.mem_singleton] at hg
        subst hg
        simp only [Gate.okBool, Bool.and_eq_true, bne_iff_ne, ne_eq, one_ne_zero,
          not_false_eq_true, and_true]
        refine ⟨?_, by simp [Desc.held, flagDesc]⟩
        have h1 := (held_iff (flagDesc d) d.numMsgs (fW hm)).mpr (Or.inr ⟨d.numMsgs - 1,
          (inReg_flagDesc hm _ _).mpr ⟨by omega, rfl⟩, by
            change dirOk ((List.map Message.dir (flagMsgs d.msgs)).getD _ _) _ _ = true
            rw [flagMsgs_dirs hm, hlast]; simp [dirOk]; omega⟩)
        exact h1
      · have : (flagDesc d).blocks.getD i [] = [] := by
          simp [flagDesc, List.getD_eq_getElem?_getD, show ¬ i < d.numMsgs + 1 by omega]
        rw [this] at hg; simp at hg

/-! ## The reject-flag transformation -/

/-- **The reject-flag description**: `d` in parallel with the flag game. -/
def rejectDesc (d : Desc) : Desc := pairDesc d (flagDesc d)

section Reject

variable {d : Desc} (hd : d.Valid) (hm : 1 ≤ d.numMsgs) (hlast : LastToVerifier d)

include hd hm hlast in
theorem rejectDesc_valid : (rejectDesc d).Valid :=
  pairDesc_valid (numMsgs_flagDesc hm).symm (flagMsgs_dirs hm).symm hd (flagDesc_valid hd hm hlast)

include hm in
theorem numMsgs_rejectDesc : (rejectDesc d).numMsgs = d.numMsgs :=
  numMsgs_pairDesc (numMsgs_flagDesc hm).symm

include hm in
theorem schedule_rejectDesc :
    (rejectDesc d).msgs.map Message.dir = d.msgs.map Message.dir :=
  dirs_pairDesc (numMsgs_flagDesc hm).symm

include hd hm hlast in
/-- **Soundness of the reject flag**: the game value is unchanged. -/
theorem value_rejectDesc : value (rejectDesc d) = value d := by
  rw [rejectDesc, value_pairDesc (numMsgs_flagDesc hm).symm hd (flagDesc_valid hd hm hlast),
    value_flagDesc hm, mul_one]

include hd hm hlast in
/-- **Every acceptance probability in `[0, value d]` is attained** by a prover of the
reject-flag description. -/
theorem exists_accept_rejectDesc {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ value d) :
    ∃ P : Prover (rejectDesc d), accept P = t := by
  obtain ⟨n, hn⟩ : ∃ n, n + 1 = d.numMsgs := ⟨d.numMsgs - 1, by omega⟩
  obtain ⟨Popt, hPopt⟩ := value_attained d
  set v := value d
  set q : ℝ := if v = 0 then 0 else t / v
  have hv0 : 0 ≤ v := (value_mem_Icc d).1
  have hq0 : 0 ≤ q := by
    simp only [q]; split_ifs
    · exact le_rfl
    · exact div_nonneg ht0 hv0
  have hq1 : q ≤ 1 := by
    simp only [q]; split_ifs with h
    · exact zero_le_one
    · exact div_le_one_of_le₀ ht hv0
  have hqt : v * q = t := by
    simp only [q]; split_ifs with h
    · rw [h] at ht ⊢; simp; linarith
    · field_simp
  have hnum : (pairDesc d (flagDesc d)).numMsgs = d.numMsgs := numMsgs_pairDesc (numMsgs_flagDesc hm).symm
  have h₁ : IsStrategy (pairDesc d (flagDesc d)).numMsgs (stratOp Popt) := by
    rw [hnum]; exact opStrategy_isStrategy Popt
  have h₂ := nonAdaptive_isStrategy (X := Reg (flagDesc d)) (flagSigma_isDensity (d := d) hq0 hq1)
    (pairDesc d (flagDesc d)).numMsgs
  obtain ⟨P, hP⟩ := (pairData d (flagDesc d) (numMsgs_flagDesc hm).symm hd
    (flagDesc_valid hd hm hlast)).exists_accept_mul h₁ h₂
  refine ⟨P, ?_⟩
  change accept P = t
  rw [hP]
  have e₁ : (trace (testerAt d (pairDesc d (flagDesc d)).numMsgs *
      stratOp Popt (pairDesc d (flagDesc d)).numMsgs)).re = v := by
    rw [hnum, ← hPopt, accept_eq_pairing]; rfl
  have e₂ : (trace (testerAt (flagDesc d) (pairDesc d (flagDesc d)).numMsgs *
      nonAdaptive (X := Reg (flagDesc d)) (flagSigma d q) (pairDesc d (flagDesc d)).numMsgs)).re =
      q := by
    rw [hnum, ← hn]; exact pairing_flagSigma hm hn q
  rw [e₁, e₂, hqt]

include hd hm hlast in
/-- **Exact half acceptance**: if `d` has value at least `1/2`, some prover of the
reject-flag description is accepted with probability exactly `1/2`. -/
theorem exists_accept_half (hv : (1 : ℝ) / 2 ≤ value d) :
    ∃ P : Prover (rejectDesc d), accept P = 1 / 2 :=
  exists_accept_rejectDesc hd hm hlast (by norm_num) hv

end Reject

/-- The standard schedule ends with a message to the verifier. -/
theorem lastToVerifier_of_hasSchedule {d : Desc} {k : ℕ} (h : d.HasSchedule k) (hk : 1 ≤ k) :
    LastToVerifier d := by
  unfold LastToVerifier
  rw [h, Desc.numMsgs_of_hasSchedule h]
  simp [stdSchedule, List.getD_eq_getElem?_getD, show k - 1 < k by omega]

end ShiQIP
