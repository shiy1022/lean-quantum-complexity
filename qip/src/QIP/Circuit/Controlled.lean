/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Circuit.Toffoli

/-!
# Q28 — controlled circuits in H/S/T/X/CNOT, exactly

For a control wire `c` and a clean ancilla wire `a`, `ctrlInstr c a g` is a controlled
version of the instruction `g`:

* `X` → `CNOT(c, ·)`;
* `CNOT(i, j)` → Toffoli `(c, i; j)`;
* `S` → the phase polynomial `T_c T_i CNOT(c,i) T_i† CNOT(c,i)`, which gives `i^{c·x}`;
* `T` → Toffoli `(c, i; a)`, then `T_a`, then Toffoli `(c, i; a)`, which needs `a = 0`;
* `H` → `S† H T† CNOT(c,i) T H S`, the identity `S H T X T† H S† = H`.

**Semantics** (`runLayer_ctrlInstr`, `runLayer_ctrlInstrs`). On every state that is clean in
`a` (zero amplitude when `a = 1`) and for every circuit avoiding `c` and `a`, the controlled
circuit computes `y ↦ if y c then (U ψ) y else ψ y`, exactly with phases. This is
`|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`. Cleanliness of `a` is preserved. Each instruction expands into at
most `67` instructions (`length_ctrlInstrs_le`).

The proof rests on *locality* (`runLayer_sliceEq`): a circuit avoiding wire `w` acts
separately on the two slices `w = 0` and `w = 1`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ShiQIP

open Matrix ShiQuantum ShiShallow

variable {n : ℕ}

/-! ## Locality -/

/-- Agreement of two states on the slice `{z | z w = b}`. -/
def SliceEq (w : Fin n) (b : Bool) (φ φ' : QState n) : Prop := ∀ z, z w = b → φ z = φ' z

/-- A state is clean in `a` if it has no amplitude on `a = 1`. -/
def Clean (a : Fin n) (φ : QState n) : Prop := ∀ z, z a = true → φ z = 0

theorem apply1_sliceEq (U : Matrix Bool Bool ℂ) {i w : Fin n} (hiw : w ≠ i) {b : Bool}
    {φ φ' : QState n} (h : SliceEq w b φ φ') : SliceEq w b (apply1 U i φ) (apply1 U i φ') := by
  intro z hz
  simp only [apply1]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [h _ (by rw [Function.update_of_ne hiw]; exact hz)]

theorem instr_apply_sliceEq (g : Instr n) {w : Fin n} (hw : w ∉ g.support) {b : Bool}
    {φ φ' : QState n} (h : SliceEq w b φ φ') : SliceEq w b (g.apply φ) (g.apply φ') := by
  cases g with
  | h i => exact apply1_sliceEq _ (by simpa [Instr.support] using hw) h
  | s i => exact apply1_sliceEq _ (by simpa [Instr.support] using hw) h
  | t i => exact apply1_sliceEq _ (by simpa [Instr.support] using hw) h
  | x i => exact apply1_sliceEq _ (by simpa [Instr.support] using hw) h
  | cnot i j hij =>
    intro z hz
    have hwj : w ≠ j := by
      intro e; apply hw; simp [Instr.support, e]
    exact h _ (by rw [Function.update_of_ne hwj]; exact hz)

theorem runLayer_nil (ψ : QState n) : runLayer ([] : List (Instr n)) ψ = ψ := rfl

theorem runLayer_cons (g : Instr n) (l : List (Instr n)) (ψ : QState n) :
    runLayer (g :: l) ψ = runLayer l (g.apply ψ) := rfl

/-- **Locality**: a circuit avoiding `w` respects agreement on each `w`-slice. -/
theorem runLayer_sliceEq {w : Fin n} {b : Bool} :
    ∀ (l : List (Instr n)), (∀ g ∈ l, w ∉ g.support) → ∀ {φ φ' : QState n},
      SliceEq w b φ φ' → SliceEq w b (runLayer l φ) (runLayer l φ')
  | [], _, _, _, h => h
  | g :: l, hl, _, _, h => by
    rw [runLayer_cons, runLayer_cons]
    exact runLayer_sliceEq l (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
      (instr_apply_sliceEq g (hl g List.mem_cons_self) h)

theorem instr_apply_zero (g : Instr n) : g.apply (0 : QState n) = 0 := by
  funext z
  cases g <;> simp [Instr.apply, apply1, cnotState]

theorem Clean.apply {a : Fin n} {φ : QState n} (h : Clean a φ) (g : Instr n)
    (ha : a ∉ g.support) : Clean a (g.apply φ) := by
  intro z hz
  have := instr_apply_sliceEq g ha (φ' := 0) (fun z hz => h z hz) z hz
  rw [this, instr_apply_zero]; rfl

/-! ## Controlled instructions -/

/-- `S† = S³`. -/
def sdg (w : Fin n) : List (Instr n) := List.replicate 3 (.s w)

/-- The controlled version of one instruction, with control `c` and clean ancilla `a`. -/
def ctrlInstr (c a : Fin n) : Instr n → List (Instr n)
  | .x i => if h : c ≠ i then [.cnot c i h] else []
  | .cnot i j hij => if h : c ≠ i ∧ c ≠ j then toffoliInstrs c i j h.1 h.2 hij else []
  | .s i => if h : c ≠ i then [.t c, .t i, .cnot c i h] ++ tdg i ++ [.cnot c i h] else []
  | .t i => if h : c ≠ i ∧ c ≠ a ∧ i ≠ a then
      toffoliInstrs c i a h.1 h.2.1 h.2.2 ++ [.t a] ++ toffoliInstrs c i a h.1 h.2.1 h.2.2
    else []
  | .h i => if h : c ≠ i then sdg i ++ [.h i] ++ tdg i ++ [.cnot c i h, .t i, .h i, .s i]
    else []

theorem apply_s (i : Fin n) (ψ : QState n) (y : Bits n) :
    (Instr.s i).apply ψ y = (if y i then Complex.I else 1) * ψ y := by
  simp only [Instr.apply, apply1, Fintype.sum_bool, sMat, of_apply]
  cases h : y i <;> simp [update_of_eq h]

theorem runLayer_toffoli' {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ψ : QState n) : runLayer (toffoliInstrs a b c hab hac hbc) ψ =
      fun y => ψ (Function.update y c (xor (y c) (y a && y b))) :=
  funext (runLayer_toffoli a b c hab hac hbc ψ)

/-- Controlled `X`. -/
theorem runLayer_ctrl_x {c a i : Fin n} (hci : c ≠ i) (ψ : QState n) (y : Bits n) :
    runLayer (ctrlInstr c a (.x i)) ψ y = if y c then (Instr.x i).apply ψ y else ψ y := by
  simp only [ctrlInstr, dif_pos hci]
  change ψ (cnotFun c i y) = _
  rw [apply_x]
  cases hc : y c
  · simp [cnotFun, hc, update_of_eq]
  · simp [cnotFun, hc]

/-- Controlled `CNOT` (a Toffoli). -/
theorem runLayer_ctrl_cnot {c a i j : Fin n} (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j)
    (ψ : QState n) (y : Bits n) :
    runLayer (ctrlInstr c a (.cnot i j hij)) ψ y =
      if y c then (Instr.cnot i j hij).apply ψ y else ψ y := by
  simp only [ctrlInstr, dif_pos (And.intro hci hcj)]
  rw [runLayer_toffoli, apply_cnot]
  cases hc : y c
  · simp [update_of_eq]
  · simp [cnotFun, Bool.xor_comm]

/-- Controlled `S`. -/
theorem runLayer_ctrl_s {c a i : Fin n} (hci : c ≠ i) (ψ : QState n) (y : Bits n) :
    runLayer (ctrlInstr c a (.s i)) ψ y = if y c then (Instr.s i).apply ψ y else ψ y := by
  have hic := hci.symm
  simp only [ctrlInstr, dif_pos hci, tdg, List.replicate, List.cons_append, List.nil_append,
    runLayer_cons]
  simp only [runLayer, List.foldl_nil, apply_t, apply_cnot, apply_s, cnotFun,
    Function.update_apply, if_true]
  have h8 := tPhase_pow_eight
  have h4 := tPhase_pow_four
  have h2 : Complex.exp (Complex.I * Real.pi / 4) ^ 2 = Complex.I := by
    rw [← Complex.exp_nat_mul]
    have : ((2 : ℕ) : ℂ) * (Complex.I * Real.pi / 4) = (Real.pi / 2 : ℝ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]; simp
  generalize Complex.exp (Complex.I * Real.pi / 4) = w at h8 h4 h2 ⊢
  cases hc : y c <;> cases hi : y i <;> simp [hi, hci, update_of_eq] <;> ring_nf <;>
    rw [pow_eq_pow_mod_eight h8] <;> norm_num [h2] <;> ring

/-- Controlled `T`, through a Toffoli into the clean ancilla. -/
theorem runLayer_ctrl_t {c a i : Fin n} (hci : c ≠ i) (hca : c ≠ a) (hia : i ≠ a)
    {ψ : QState n} (hψ : Clean a ψ) (y : Bits n) :
    runLayer (ctrlInstr c a (.t i)) ψ y = if y c then (Instr.t i).apply ψ y else ψ y := by
  simp only [ctrlInstr, dif_pos (And.intro hci (And.intro hca hia))]
  rw [runLayer_append, runLayer_append, runLayer_toffoli', runLayer_toffoli']
  change (Instr.t a).apply (fun y => ψ (Function.update y a (xor (y a) (y c && y i))))
    (Function.update y a (xor (y a) (y c && y i))) = _
  rw [apply_t]
  simp only [Function.update_self, Function.update_idem, Function.update_of_ne hca,
    Function.update_of_ne hia, apply_t]
  cases ha : y a
  · cases hc : y c <;> cases hi : y i <;> simp [ha, hc, hi, update_of_eq]
  · rw [hψ y ha]
    cases hc : y c <;> cases hi : y i <;> simp [ha, hc, hi, update_of_eq, hψ y ha]

theorem apply1_apply1 (U V : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    apply1 U i (apply1 V i ψ) = apply1 (U * V) i ψ := by
  rw [← oneQubitMat_mulVec, ← oneQubitMat_mulVec, ← oneQubitMat_mulVec, mulVec_mulVec,
    oneQubitMat_mul]

theorem apply1_one (i : Fin n) (ψ : QState n) : apply1 1 i ψ = ψ := by
  funext y
  simp only [apply1, Fintype.sum_bool, one_apply]
  cases h : y i <;> simp [update_of_eq h]

theorem runLayer_tdg (i : Fin n) (ψ : QState n) : runLayer (tdg i) ψ = apply1 (tMat ^ 7) i ψ := by
  simp only [tdg, List.replicate, runLayer_cons, runLayer_nil, Instr.apply, apply1_apply1]
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]

theorem runLayer_sdg (i : Fin n) (ψ : QState n) : runLayer (sdg i) ψ = apply1 (sMat ^ 3) i ψ := by
  simp only [sdg, List.replicate, runLayer_cons, runLayer_nil, Instr.apply, apply1_apply1]
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]

theorem tPhase_eq : Complex.exp (Complex.I * Real.pi / 4) =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

/-- `W = S H T` conjugates `X` to `H`. -/
theorem sht_x_sht_dag : (sMat * hMat * tMat) * xMat * (sMat * hMat * tMat)ᴴ = hMat := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℝ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  ext a b
  cases a <;> cases b <;>
    simp [mul_apply, hMat, sMat, tMat, xMat, conjTranspose_apply, tPhase_eq] <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq, map_ofNat] <;> ring_nf

theorem sht_unitary : (sMat * hMat * tMat) * (sMat * hMat * tMat)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp ((Matrix.unitaryGroup Bool ℂ).mul_mem
    ((Matrix.unitaryGroup Bool ℂ).mul_mem sMat_mem_unitaryGroup hMat_mem_unitaryGroup)
    tMat_mem_unitaryGroup)
  rwa [Matrix.star_eq_conjTranspose] at h

/-- Controlled `H`, from `S H T · X · (S H T)† = H` and `(S H T)(S H T)† = 1`. -/
theorem runLayer_ctrl_h {c a i : Fin n} (hci : c ≠ i) (ψ : QState n) (y : Bits n) :
    runLayer (ctrlInstr c a (.h i)) ψ y = if y c then (Instr.h i).apply ψ y else ψ y := by
  simp only [ctrlInstr, dif_pos hci]
  have hA : runLayer (sdg i ++ [Instr.h i] ++ tdg i) ψ =
      apply1 (sMat * hMat * tMat)ᴴ i ψ := by
    rw [runLayer_append, runLayer_append, runLayer_sdg, runLayer_tdg]
    change apply1 (tMat ^ 7) i (apply1 hMat i (apply1 (sMat ^ 3) i ψ)) = _
    rw [apply1_apply1, apply1_apply1, tMat_pow_seven,
      show sMat ^ 3 = sMat * sMat * sMat by simp [pow_succ], sMat_cube]
    congr 1
    simp only [conjTranspose_mul, hMat_conjTranspose, Matrix.mul_assoc]
  have hB : ∀ φ : QState n, runLayer [Instr.t i, .h i, .s i] φ =
      apply1 (sMat * hMat * tMat) i φ := by
    intro φ
    simp only [runLayer_cons, runLayer_nil, Instr.apply, apply1_apply1, Matrix.mul_assoc]
  rw [show sdg i ++ [Instr.h i] ++ tdg i ++ [Instr.cnot c i hci, .t i, .h i, .s i] =
      (sdg i ++ [Instr.h i] ++ tdg i) ++ ([Instr.cnot c i hci] ++ [.t i, .h i, .s i]) by simp,
    runLayer_append, runLayer_append, hA, hB]
  cases hc : y c
  · have hs : SliceEq c false (runLayer [Instr.cnot c i hci] (apply1 (sMat * hMat * tMat)ᴴ i ψ))
        (apply1 (sMat * hMat * tMat)ᴴ i ψ) := by
      intro z hz
      change apply1 _ i ψ (cnotFun c i z) = _
      simp [cnotFun, hz, update_of_eq]
    rw [apply1_sliceEq _ hci hs y hc, apply1_apply1, sht_unitary, apply1_one]
    simp
  · have hs : SliceEq c true (runLayer [Instr.cnot c i hci] (apply1 (sMat * hMat * tMat)ᴴ i ψ))
        (apply1 xMat i (apply1 (sMat * hMat * tMat)ᴴ i ψ)) := by
      intro z hz
      change apply1 _ i ψ (cnotFun c i z) = (Instr.x i).apply _ z
      rw [apply_x]
      simp [cnotFun, hz]
    rw [apply1_sliceEq _ hci hs y hc, apply1_apply1, apply1_apply1, sht_x_sht_dag]
    simp [Instr.apply]

/-! ## Controlled circuits -/

/-- The controlled version of a circuit. -/
def ctrlInstrs (c a : Fin n) (l : List (Instr n)) : List (Instr n) := l.flatMap (ctrlInstr c a)

/-- **One controlled instruction**, on states clean in the ancilla. -/
theorem runLayer_ctrlInstr {c a : Fin n} (hca : c ≠ a) (g : Instr n) (hc : c ∉ g.support)
    (ha : a ∉ g.support) {ψ : QState n} (hψ : Clean a ψ) (y : Bits n) :
    runLayer (ctrlInstr c a g) ψ y = if y c then g.apply ψ y else ψ y := by
  cases g with
  | h i => exact runLayer_ctrl_h (by simpa [Instr.support] using hc) ψ y
  | s i => exact runLayer_ctrl_s (by simpa [Instr.support] using hc) ψ y
  | t i =>
    have hia : i ≠ a := fun e => ha (by simp [Instr.support, e])
    exact runLayer_ctrl_t (by simpa [Instr.support] using hc) hca hia hψ y
  | x i => exact runLayer_ctrl_x (by simpa [Instr.support] using hc) ψ y
  | cnot i j hij =>
    have h1 : c ≠ i := fun e => hc (by simp [Instr.support, e])
    have h2 : c ≠ j := fun e => hc (by simp [Instr.support, e])
    exact runLayer_ctrl_cnot hij h1 h2 ψ y

theorem Clean.runLayer {a : Fin n} : ∀ (l : List (Instr n)), (∀ g ∈ l, a ∉ g.support) →
    ∀ {φ : QState n}, Clean a φ → Clean a (runLayer l φ)
  | [], _, _, h => h
  | g :: l, hl, _, h => by
    rw [runLayer_cons]
    exact Clean.runLayer l (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
      (h.apply g (hl g List.mem_cons_self))

/-- **Controlled circuits are exact**: for a circuit avoiding the control `c` and the ancilla
`a`, on every state clean in `a`, the controlled circuit is `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`. -/
theorem runLayer_ctrlInstrs {c a : Fin n} (hca : c ≠ a) :
    ∀ (l : List (Instr n)), (∀ g ∈ l, c ∉ g.support ∧ a ∉ g.support) →
      ∀ {ψ : QState n}, Clean a ψ → ∀ y,
        runLayer (ctrlInstrs c a l) ψ y = if y c then runLayer l ψ y else ψ y
  | [], _, ψ, _, y => by simp [ctrlInstrs, runLayer_nil]
  | g :: l, hl, ψ, hψ, y => by
    have hg := hl g List.mem_cons_self
    have hl' : ∀ g' ∈ l, c ∉ g'.support ∧ a ∉ g'.support :=
      fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')
    have e : ctrlInstrs c a (g :: l) = ctrlInstr c a g ++ ctrlInstrs c a l := by
      simp [ctrlInstrs]
    have hφ : runLayer (ctrlInstr c a g) ψ = fun z => if z c then g.apply ψ z else ψ z :=
      funext (runLayer_ctrlInstr hca g hg.1 hg.2 hψ)
    have hclean : Clean a (fun z => if z c then g.apply ψ z else ψ z) := by
      intro z hz
      dsimp only
      split_ifs
      · exact hψ.apply g hg.2 z hz
      · exact hψ z hz
    rw [e, runLayer_append, hφ, runLayer_ctrlInstrs hca l hl' hclean y, runLayer_cons]
    cases hc : y c
    · simp
    · simp only [if_true]
      exact runLayer_sliceEq l (fun g' hg' => (hl' g' hg').1)
        (fun z hz => by simp [hz]) y hc

/-- The controlled circuit keeps the ancilla clean. -/
theorem clean_ctrlInstrs {c a : Fin n} (hca : c ≠ a) (l : List (Instr n))
    (hl : ∀ g ∈ l, c ∉ g.support ∧ a ∉ g.support) {ψ : QState n} (hψ : Clean a ψ) :
    Clean a (runLayer (ctrlInstrs c a l) ψ) := by
  intro z hz
  rw [runLayer_ctrlInstrs hca l hl hψ z]
  split_ifs
  · exact Clean.runLayer l (fun g hg => (hl g hg).2) hψ z hz
  · exact hψ z hz

theorem length_toffoliInstrs {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (toffoliInstrs a b c hab hac hbc).length = 33 := by
  simp [toffoliInstrs, cczInstrs, tdg]

theorem length_ctrlInstr_le (c a : Fin n) (g : Instr n) : (ctrlInstr c a g).length ≤ 67 := by
  cases g <;> simp only [ctrlInstr] <;> split_ifs <;>
    simp [length_toffoliInstrs, tdg, sdg]

/-- **Expansion bound**: each instruction becomes at most `67` instructions. -/
theorem length_ctrlInstrs_le (c a : Fin n) (l : List (Instr n)) :
    (ctrlInstrs c a l).length ≤ 67 * l.length := by
  induction l with
  | nil => simp [ctrlInstrs]
  | cons g l ih =>
    have e : ctrlInstrs c a (g :: l) = ctrlInstr c a g ++ ctrlInstrs c a l := by
      simp [ctrlInstrs]
    rw [e, List.length_append, List.length_cons]
    have := length_ctrlInstr_le c a g
    omega

/-! ## Description syntax -/

def sdgGates (w : ℕ) : List Gate := List.replicate 3 (.s w)

/-- The controlled version of one gate, as description syntax. -/
def ctrlGate (c a : ℕ) : Gate → List Gate
  | .x i => [.cnot c i]
  | .cnot i j => toffoliGates c i j
  | .s i => [.t c, .t i, .cnot c i] ++ tdgGates i ++ [.cnot c i]
  | .t i => toffoliGates c i a ++ [.t a] ++ toffoliGates c i a
  | .h i => sdgGates i ++ [.h i] ++ tdgGates i ++ [.cnot c i, .t i, .h i, .s i]

/-- The controlled version of a gate list. -/
def ctrlGates (c a : ℕ) (gs : List Gate) : List Gate := gs.flatMap (ctrlGate c a)

theorem length_ctrlGates_le (c a : ℕ) (gs : List Gate) :
    (ctrlGates c a gs).length ≤ 67 * gs.length := by
  induction gs with
  | nil => simp [ctrlGates]
  | cons g gs ih =>
    have e : ctrlGates c a (g :: gs) = ctrlGate c a g ++ ctrlGates c a gs := by simp [ctrlGates]
    rw [e, List.length_append, List.length_cons]
    have : (ctrlGate c a g).length ≤ 67 := by
      cases g <;> simp [ctrlGate, length_toffoliGates, tdgGates, sdgGates]
    omega

/-- The support of a translated gate is its wire list. -/
theorem mem_support_of_toInstr? {N : ℕ} {g : Gate} {ι : Instr N} (hg : g.toInstr? N = some ι)
    (w : Fin N) : w ∈ ι.support ↔ (w : ℕ) ∈ g.wires := by
  cases g with
  | h i => simp only [Gate.toInstr?] at hg; split_ifs at hg; cases hg
           simp [Instr.support, Gate.wires, Fin.ext_iff]
  | s i => simp only [Gate.toInstr?] at hg; split_ifs at hg; cases hg
           simp [Instr.support, Gate.wires, Fin.ext_iff]
  | t i => simp only [Gate.toInstr?] at hg; split_ifs at hg; cases hg
           simp [Instr.support, Gate.wires, Fin.ext_iff]
  | x i => simp only [Gate.toInstr?] at hg; split_ifs at hg; cases hg
           simp [Instr.support, Gate.wires, Fin.ext_iff]
  | cnot i j => simp only [Gate.toInstr?] at hg; split_ifs at hg; cases hg
                simp [Instr.support, Gate.wires, Fin.ext_iff]

/-- **The syntax translates exactly** to the controlled instructions. -/
theorem filterMap_ctrlGate {N : ℕ} (c a : Fin N) (hca : c ≠ a) {g : Gate} {ι : Instr N}
    (hg : g.toInstr? N = some ι) (hc : (c : ℕ) ∉ g.wires) (ha : (a : ℕ) ∉ g.wires) :
    (ctrlGate c a g).filterMap (Gate.toInstr? N) = ctrlInstr c a ι := by
  have hca' : (c : ℕ) ≠ a := fun e => hca (Fin.ext e)
  cases g with
  | h i =>
    simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
    have hci : (c : ℕ) ≠ i := fun e => hc (by simp [Gate.wires, e])
    have hci' : c ≠ ⟨i, hi⟩ := fun e => hci (congrArg Fin.val e)
    simp [ctrlGate, ctrlInstr, hci', sdgGates, sdg, tdgGates, tdg, Gate.toInstr?, hi, c.isLt,
      hci, List.replicate]
  | s i =>
    simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
    have hci : (c : ℕ) ≠ i := fun e => hc (by simp [Gate.wires, e])
    have hci' : c ≠ ⟨i, hi⟩ := fun e => hci (congrArg Fin.val e)
    simp [ctrlGate, ctrlInstr, hci', tdgGates, tdg, Gate.toInstr?, hi, c.isLt, hci,
      List.replicate]
  | t i =>
    simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
    have hci : (c : ℕ) ≠ i := fun e => hc (by simp [Gate.wires, e])
    have hia : i ≠ (a : ℕ) := fun e => ha (by simp [Gate.wires, e])
    have h1 : c ≠ ⟨i, hi⟩ := fun e => hci (congrArg Fin.val e)
    have h3 : (⟨i, hi⟩ : Fin N) ≠ a := fun e => hia (congrArg Fin.val e)
    have ht := filterMap_toffoliGates c ⟨i, hi⟩ a h1 hca h3
    simp only [Fin.val_mk] at ht
    simp only [ctrlGate, ctrlInstr, dif_pos (And.intro h1 (And.intro hca h3)),
      List.filterMap_append, ht]
    simp [Gate.toInstr?, a.isLt]
  | x i =>
    simp only [Gate.toInstr?] at hg; split_ifs at hg with hi; cases hg
    have hci : (c : ℕ) ≠ i := fun e => hc (by simp [Gate.wires, e])
    have hci' : c ≠ ⟨i, hi⟩ := fun e => hci (congrArg Fin.val e)
    simp [ctrlGate, ctrlInstr, hci', Gate.toInstr?, hi, c.isLt, hci]
  | cnot i j =>
    simp only [Gate.toInstr?] at hg; split_ifs at hg with hij; cases hg
    have hci : (c : ℕ) ≠ i := fun e => hc (by simp [Gate.wires, e])
    have hcj : (c : ℕ) ≠ j := fun e => hc (by simp [Gate.wires, e])
    have h1 : c ≠ ⟨i, hij.1⟩ := fun e => hci (congrArg Fin.val e)
    have h2 : c ≠ ⟨j, hij.2.1⟩ := fun e => hcj (congrArg Fin.val e)
    have h3 : (⟨i, hij.1⟩ : Fin N) ≠ ⟨j, hij.2.1⟩ := fun e => hij.2.2 (congrArg Fin.val e)
    have ht := filterMap_toffoliGates c ⟨i, hij.1⟩ ⟨j, hij.2.1⟩ h1 h2 h3
    simp only [Fin.val_mk] at ht
    simp only [ctrlGate, ctrlInstr, dif_pos (And.intro h1 h2), ht]

/-- **The controlled gate list translates to the controlled circuit of its translation.** -/
theorem filterMap_ctrlGates {N : ℕ} (c a : Fin N) (hca : c ≠ a) :
    ∀ (gs : List Gate), (∀ g ∈ gs, (g.toInstr? N).isSome ∧ (c : ℕ) ∉ g.wires ∧
      (a : ℕ) ∉ g.wires) →
      (ctrlGates c a gs).filterMap (Gate.toInstr? N) =
        ctrlInstrs c a (gs.filterMap (Gate.toInstr? N))
  | [], _ => by simp [ctrlGates, ctrlInstrs]
  | g :: gs, h => by
    obtain ⟨hs, hc, ha⟩ := h g List.mem_cons_self
    obtain ⟨ι, hι⟩ := Option.isSome_iff_exists.mp hs
    have e : ctrlGates c a (g :: gs) = ctrlGate c a g ++ ctrlGates c a gs := by
      simp [ctrlGates]
    rw [e, List.filterMap_append, filterMap_ctrlGate c a hca hι hc ha,
      filterMap_ctrlGates c a hca gs fun g' hg' => h g' (List.mem_cons_of_mem _ hg'),
      List.filterMap_cons, hι]
    simp [ctrlInstrs]

end ShiQIP
