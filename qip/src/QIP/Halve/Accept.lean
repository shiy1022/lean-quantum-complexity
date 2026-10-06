import QIP.Halve.Steps


/-!
# Q31 — acceptance of the halved description

* `runLayer_support`: a circuit acting on a set of labels as an involution keeps states supported
  there (by norm preservation).
* The zero test of the final block (`ztS`, `ztA`) and the sums over `Φ`-states (`sum_Φ`).
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

/-- **Support preservation.** If a circuit acts on the labels in `P` by an involution of `P`, it
keeps states supported in `P` supported in `P`. -/
theorem runLayer_support {M : ℕ} (l : List (Instr M)) (P : Bits M → Prop) [DecidablePred P]
    (f : Bits M → Bits M) (hf : Function.Involutive f) (hPf : ∀ y, P (f y) ↔ P y) (ψ : QState M)
    (hψ : ∀ y, ¬ P y → ψ y = 0) (hl : ∀ y, P y → runLayer l ψ y = ψ (f y)) :
    ∀ y, ¬ P y → runLayer l ψ y = 0 := by
  have hn : nsq (runLayer l ψ) = nsq ψ := by
    rw [← layerMat_mulVec]; exact nsq_unitary (layerMat_mem_unitaryGroup l) ψ
  have hsplit : ∀ φ : QState M, nsq φ = (∑ y, if P y then ‖φ y‖ ^ 2 else 0) +
      ∑ y, if P y then 0 else ‖φ y‖ ^ 2 := by
    intro φ
    rw [nsq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  have h1 : (∑ y, if P y then ‖ψ y‖ ^ 2 else 0) = ∑ y, if P y then ‖runLayer l ψ y‖ ^ 2 else 0 := by
    rw [← Equiv.sum_comp hf.toPerm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Function.Involutive.coe_toPerm, hPf]
    split_ifs with h
    · rw [hl y h]
    · rfl
  have h2 : (∑ y, if P y then 0 else ‖ψ y‖ ^ 2) = 0 :=
    Finset.sum_eq_zero fun y _ => by by_cases h : P y <;> simp [h, hψ]
  have h3 : (∑ y, if P y then 0 else ‖runLayer l ψ y‖ ^ 2) = 0 := by
    have := hsplit (runLayer l ψ)
    rw [hn, hsplit ψ, h1, h2] at this
    linarith
  intro y hy
  have hle : ‖runLayer l ψ y‖ ^ 2 ≤ 0 := by
    rw [← h3]
    have := Finset.single_le_sum (f := fun y => if P y then (0 : ℝ) else ‖runLayer l ψ y‖ ^ 2)
      (fun y _ => by split_ifs <;> positivity) (Finset.mem_univ y)
    simpa [hy] using this
  have : ‖runLayer l ψ y‖ = 0 := by nlinarith [norm_nonneg (runLayer l ψ y)]
  exact norm_eq_zero.mp this


variable {d : Desc} {n : ℕ} {N₀ : Type} [Fintype N₀] [DecidableEq N₀]

/-! ## Sums over `Φ`-states -/

variable (d n) in
/-- The label with working copy `x`, coin `b`, message wires `β` and clean control wires. -/
def asm (b : Bool) (x : Qubits d.totalWires) (β : MB d n) : Qubits (halveDesc d n).totalWires :=
  fun w => if h : (w : ℕ) < d.totalWires then x ⟨w, h⟩ else if (w : ℕ) = d.totalWires then b
    else if h' : hPriv d ≤ (w : ℕ) then β ⟨w, h'⟩ else false

theorem ctlOK_asm (b : Bool) (x : Qubits d.totalWires) (β : MB d n) : ctlOK b (asm d n b x β) := by
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  refine ⟨?_, ?_, ?_, fun w h1 h2 => ?_⟩
  · simp [asm, coinW_val]
  · have := outW_val (d := d) (n := n)
    simp only [asm]; split_ifs <;> first | rfl | (exfalso; omega)
  · have := caW_val (d := d) (n := n)
    simp only [asm]; split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [asm]; split_ifs <;> first | rfl | (exfalso; omega)

theorem workPart_asm (b : Bool) (x : Qubits d.totalWires) (β : MB d n) : workPart (asm d n b x β) = x := by
  funext w; simp [workPart, asm, workEmb, w.2]

theorem msgPart_asm (b : Bool) (x : Qubits d.totalWires) (β : MB d n) : msgPart (asm d n b x β) = β := by
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  funext u
  have hu := u.2
  simp only [msgPart, asm]
  rw [dif_neg (by omega), if_neg (by omega), dif_pos hu]

theorem asm_eq {b : Bool} {y : Qubits (halveDesc d n).totalWires} (hy : ctlOK b y) :
    asm d n b (workPart y) (msgPart y) = y := by
  funext w
  simp only [asm, workPart, msgPart]
  split_ifs with h1 h2 h3
  · rfl
  · rw [← hy.1]; congr 1; exact Fin.ext h2.symm
  · rfl
  · by_cases e1 : (w : ℕ) = d.totalWires + 1
    · rw [show w = outW d n from Fin.ext e1, hy.2.1]
    by_cases e2 : (w : ℕ) = d.totalWires + 2
    · rw [show w = caW d n from Fin.ext e2, hy.2.2.1]
    rw [hy.2.2.2 w (by omega) (by omega)]

theorem asm_injective (b : Bool) : Function.Injective fun p : Qubits d.totalWires × MB d n => asm d n b p.1 p.2 := by
  intro p q h
  have h1 := congrArg workPart h
  have h2 := congrArg msgPart h
  simp only [workPart_asm, msgPart_asm] at h1 h2
  exact Prod.ext h1 h2

omit [Fintype N₀] [DecidableEq N₀] in
/-- **Sums over a `Φ`-state.** -/
theorem sum_Φ (b : Bool) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀)
    (g : Qubits (halveDesc d n).totalWires → ℝ) :
    ∑ y, g y * ‖Φ b v (y, μ)‖ ^ 2 = ∑ x, ∑ β, g (asm d n b x β) * ‖v (x, (μ, β))‖ ^ 2 := by
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_of_injective _ (asm_injective b) _ _ (fun y hy => ?_) (fun p => ?_)).symm
  · have : ¬ ctlOK b y := fun h => hy ⟨(workPart y, msgPart y), asm_eq h⟩
    simp [Φ, this]
  · simp only [Φ, if_pos (ctlOK_asm b p.1 p.2), workPart_asm, msgPart_asm]

/-! ## The zero test -/

theorem lt_of_mem_held0 {w : ℕ} (h : w ∈ held0 d) : w < (halveDesc d n).totalWires := by
  have := W_lt_total d n
  simp only [held0, List.mem_filter, List.mem_range] at h
  omega

theorem mem_hAnc {w : ℕ} : w ∈ hAnc d ↔ d.totalWires + 3 ≤ w ∧ w < hPriv d := by
  simp only [hAnc, List.mem_map, List.mem_range, hPriv]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨w - (d.totalWires + 3), by omega, by omega⟩

theorem lt_of_mem_hAnc {w : ℕ} (h : w ∈ hAnc d) : w < (halveDesc d n).totalWires := by
  have := hPriv_le_total d n
  have := (mem_hAnc.mp h).2
  omega

variable (d n) in
/-- The tested wires. -/
def ztS : List (Fin (halveDesc d n).totalWires) := (held0 d).pmap Fin.mk fun _ h => lt_of_mem_held0 h

variable (d n) in
/-- The zero-test ancillas. -/
def ztA : List (Fin (halveDesc d n).totalWires) := (hAnc d).pmap Fin.mk fun _ h => lt_of_mem_hAnc h

theorem map_val_ztS : (ztS d n).map Fin.val = held0 d := by
  simp [ztS, List.map_pmap]

theorem map_val_ztA : (ztA d n).map Fin.val = hAnc d := by
  simp [ztA, List.map_pmap]

theorem mem_ztA {a : Fin (halveDesc d n).totalWires} :
    a ∈ ztA d n ↔ d.totalWires + 3 ≤ (a : ℕ) ∧ (a : ℕ) < hPriv d := by
  rw [← mem_hAnc]
  constructor
  · intro h; have := List.mem_map_of_mem (f := Fin.val) h; rwa [map_val_ztA] at this
  · intro h
    rw [← map_val_ztA (n := n), List.mem_map] at h
    obtain ⟨a', ha', e⟩ := h
    rwa [show a = a' from Fin.ext e.symm]

theorem mem_ztS {s : Fin (halveDesc d n).totalWires} :
    s ∈ ztS d n ↔ (s : ℕ) < d.totalWires ∧ d.held 0 s = true := by
  have : (s : ℕ) ∈ held0 d ↔ (s : ℕ) < d.totalWires ∧ d.held 0 s = true := by
    simp [held0]
  rw [← this]
  constructor
  · intro h; have := List.mem_map_of_mem (f := Fin.val) h; rwa [map_val_ztS] at this
  · intro h
    rw [← map_val_ztS (n := n), List.mem_map] at h
    obtain ⟨a', ha', e⟩ := h
    rwa [show s = a' from Fin.ext e.symm]

theorem nodup_zt : (coinW d n :: outW d n :: (ztS d n ++ ztA d n)).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [List.map_cons, List.map_cons, List.map_append, map_val_ztS, map_val_ztA, coinW_val, outW_val]
  have h1 : (held0 d).Nodup := (List.nodup_range).filter _
  have h2 : (hAnc d).Nodup := (List.nodup_range).map (fun a b h => by omega)
  have hS : ∀ w ∈ held0 d, w < d.totalWires := fun w h => by
    simp only [held0, List.mem_filter, List.mem_range] at h; exact h.1
  have hA : ∀ w ∈ hAnc d, d.totalWires + 3 ≤ w := fun w h => (mem_hAnc.mp h).1
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or]
  refine ⟨⟨by omega, fun h => by have := hS _ h; omega, fun h => by have := hA _ h; omega⟩,
    ⟨fun h => by have := hS _ h; omega, fun h => by have := hA _ h; omega⟩,
    List.nodup_append.mpr ⟨h1, h2, fun a ha b hb e => ?_⟩⟩
  have := hS a ha; have := hA b hb; omega

theorem length_zt : (ztS d n).length ≤ (ztA d n).length := by
  have h1 := congrArg List.length (map_val_ztS (d := d) (n := n))
  have h2 := congrArg List.length (map_val_ztA (d := d) (n := n))
  simp only [List.length_map] at h1 h2
  rw [h1, h2, hAnc, List.length_map, List.length_range]

theorem ztGates_eq : ztGates (hCoin d) (hOut d) (held0 d) (hAnc d) =
    ztGates (coinW d n : ℕ) (outW d n : ℕ) ((ztS d n).map Fin.val) ((ztA d n).map Fin.val) := by
  rw [map_val_ztS, map_val_ztA]; rfl

/-- The zero test on labels with clean ancillas. -/
theorem runLayer_ztGates (ψ : QState (halveDesc d n).totalWires) (y : Qubits (halveDesc d n).totalWires)
    (hy : ∀ a ∈ ztA d n, y a = false) :
    runLayer ((ztGates (hCoin d) (hOut d) (held0 d) (hAnc d)).filterMap
      (Gate.toInstr? (halveDesc d n).totalWires)) ψ y = ψ (ztFun (coinW d n) (outW d n) (ztS d n) y) := by
  rw [ztGates_eq]
  exact runLayer_zt _ _ _ _ nodup_zt length_zt ψ y hy

theorem outW_ne_coinW : outW d n ≠ coinW d n := fun h => by
  have := congrArg Fin.val h; rw [outW_val, coinW_val] at this; omega

theorem outW_notMem_ztS : outW d n ∉ ztS d n := fun h => by
  have := (mem_ztS.mp h).1; rw [outW_val] at this; omega

theorem ztFun_apply_ne {w : Fin (halveDesc d n).totalWires} (hw : w ≠ outW d n)
    (y : Qubits (halveDesc d n).totalWires) : ztFun (coinW d n) (outW d n) (ztS d n) y w = y w := by
  simp only [ztFun]; rw [Function.update_of_ne hw]

theorem ztFun_involutive : Function.Involutive (ztFun (coinW d n) (outW d n) (ztS d n)) := by
  intro y
  have hc := ztFun_apply_ne (outW_ne_coinW (d := d) (n := n)).symm
  have hall : ∀ y : Qubits (halveDesc d n).totalWires,
      ((ztS d n).all fun s => !ztFun (coinW d n) (outW d n) (ztS d n) y s) = (ztS d n).all fun s => !y s := by
    intro y
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun s => forall_congr' fun hs => ?_
    rw [ztFun_apply_ne (fun e => outW_notMem_ztS (e ▸ hs))]
  funext w
  by_cases hw : w = outW d n
  · subst hw
    simp only [ztFun, Function.update_self]
    have := hall y
    simp only [ztFun] at this
    rw [Function.update_of_ne outW_ne_coinW.symm, this]
    cases y (outW d n) <;> cases y (coinW d n) <;> simp
  · rw [ztFun_apply_ne hw, ztFun_apply_ne hw]

theorem zero0_iff_all (y : Qubits (halveDesc d n).totalWires) :
    ((ztS d n).all fun s => !y s) = true ↔ Zero0 d (workPart y) := by
  rw [List.all_eq_true]
  constructor
  · intro h w hw
    have := h ⟨w, by have := W_lt_total d n; omega⟩ (mem_ztS.mpr ⟨w.2, hw⟩)
    have h' : y ⟨w, by have := W_lt_total d n; omega⟩ = false := by simpa using this
    exact h'
  · intro h s hs
    have := h ⟨s, (mem_ztS.mp hs).1⟩ (mem_ztS.mp hs).2
    have h' : y s = false := this
    simp [h']


/-! ## Acceptance of one memory slice -/

theorem anc_ne {a : Fin (halveDesc d n).totalWires} (ha : a ∈ ztA d n) (w : Fin (halveDesc d n).totalWires)
    (hw : (w : ℕ) < d.totalWires + 3) : a ≠ w := fun e => by
  have := (mem_ztA.mp ha).1; rw [e] at this; omega

omit [Fintype N₀] [DecidableEq N₀] in
theorem Φ_dirty {b : Bool} {v : Qubits d.totalWires × (N₀ × MB d n) → ℂ} {y : Qubits (halveDesc d n).totalWires}
    {a : Fin (halveDesc d n).totalWires} (ha : a ∈ ztA d n) (hy : y a = true) (μ : N₀) : Φ b v (y, μ) = 0 := by
  simp only [Φ]
  rw [if_neg]
  intro h
  have := h.2.2.2 a (mem_ztA.mp ha).1 (mem_ztA.mp ha).2
  rw [hy] at this; exact absurd this (by decide)

theorem norm_sq_add_of_mul {a b : ℂ} (h : a = 0 ∨ b = 0) : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rcases h with rfl | rfl <;> simp

variable (d n) in
/-- The zero test on labels. -/
def ztZ : Qubits (halveDesc d n).totalWires → Qubits (halveDesc d n).totalWires :=
  ztFun (coinW d n) (outW d n) (ztS d n)

variable (d n) in
/-- The output copy on labels. -/
def outC (hd : d.Valid) : Qubits (halveDesc d n).totalWires → Qubits (halveDesc d n).totalWires :=
  cnotFun (outD d n hd) (outW d n)

theorem ztZ_ztZ (y : Qubits (halveDesc d n).totalWires) : ztZ d n (ztZ d n y) = y := ztFun_involutive y

theorem outC_outC (hd : d.Valid) (y : Qubits (halveDesc d n).totalWires) : outC d n hd (outC d n hd y) = y :=
  cnotFun_involutive (outD_ne_outW hd) y

theorem sum_invol {X : Type} [Fintype X] {f : X → X} (hf : ∀ x, f (f x) = x) (g : X → ℝ) :
    ∑ x, g (f x) = ∑ x, g x :=
  Equiv.sum_comp (Function.Involutive.toPerm f hf) g

omit [Fintype N₀] [DecidableEq N₀] in
/-- **Acceptance of one memory slice** of the final state. -/
theorem accept_slice (hd : d.Valid) (F B : Qubits d.totalWires × (N₀ × MB d n) → ℂ) (μ : N₀) :
    (∑ y, if y (outW d n) = true then ‖runLayer ((ztGates (hCoin d) (hOut d) (held0 d) (hAnc d)).filterMap
      (Gate.toInstr? (halveDesc d n).totalWires)) ((Real.sqrt 2 : ℂ)⁻¹ • fun y =>
        Φ false F (cnotFun (outD d n hd) (outW d n) y, μ) + Φ true B (y, μ)) y‖ ^ 2 else 0) =
      (1 / 2 : ℝ) * ((∑ x, ∑ β, if outBit d x then ‖F (x, (μ, β))‖ ^ 2 else 0) +
        ∑ x, ∑ β, if Zero0 d x then ‖B (x, (μ, β))‖ ^ 2 else 0) := by
  have hP : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  change (∑ y, if y (outW d n) = true then ‖runLayer ((ztGates (hCoin d) (hOut d) (held0 d) (hAnc d)).filterMap
      (Gate.toInstr? (halveDesc d n).totalWires)) ((Real.sqrt 2 : ℂ)⁻¹ • fun y =>
        Φ false F (outC d n hd y, μ) + Φ true B (y, μ)) y‖ ^ 2 else 0) = _
  generalize hψ : ((Real.sqrt 2 : ℂ)⁻¹ • fun y => Φ false F (outC d n hd y, μ) + Φ true B (y, μ) :
    QState (halveDesc d n).totalWires) = ψ
  have hψy : ∀ y, ψ y = (Real.sqrt 2 : ℂ)⁻¹ * (Φ false F (outC d n hd y, μ) + Φ true B (y, μ)) :=
    fun y => by rw [← hψ]; rfl
  have hCa : ∀ y (a : Fin (halveDesc d n).totalWires), a ∈ ztA d n → outC d n hd y a = y a := fun y a ha => by
    simp only [outC, cnotFun]
    rw [Function.update_of_ne (anc_ne ha _ (by rw [outW_val]; omega))]
  have hCc : ∀ y, outC d n hd y (coinW d n) = y (coinW d n) := fun y => by
    simp only [outC, cnotFun]
    rw [Function.update_of_ne outW_ne_coinW.symm]
  have hZa : ∀ y (a : Fin (halveDesc d n).totalWires), a ∈ ztA d n → ztZ d n y a = y a := fun y a ha =>
    ztFun_apply_ne (anc_ne ha _ (by rw [outW_val]; omega)) y
  -- the state is supported on clean ancillas
  have hdirty : ∀ y, ¬ (∀ a ∈ ztA d n, y a = false) → ψ y = 0 := by
    intro y hy
    push Not at hy
    obtain ⟨a, ha, hya⟩ := hy
    replace hya : y a = true := by simpa using hya
    rw [hψy, Φ_dirty ha (by rw [hCa y a ha]; exact hya), Φ_dirty ha hya, add_zero, mul_zero]
  have hsupp := runLayer_support ((ztGates (hCoin d) (hOut d) (held0 d) (hAnc d)).filterMap
    (Gate.toInstr? (halveDesc d n).totalWires)) (fun y => ∀ a ∈ ztA d n, y a = false) (ztZ d n) ztZ_ztZ
    (fun y => forall₂_congr fun a ha => by rw [hZa y a ha]) ψ hdirty
    (fun y hy => runLayer_ztGates ψ y hy)
  -- reduce to a sum over the state before the test
  have h1 : (∑ y, if y (outW d n) = true then ‖runLayer ((ztGates (hCoin d) (hOut d) (held0 d) (hAnc d)).filterMap
      (Gate.toInstr? (halveDesc d n).totalWires)) ψ y‖ ^ 2 else 0) =
        ∑ y, if ztZ d n y (outW d n) = true then ‖ψ y‖ ^ 2 else 0 := by
    rw [← sum_invol ztZ_ztZ]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : ∀ a ∈ ztA d n, y a = false
    · have hy' : ∀ a ∈ ztA d n, ztZ d n y a = false := fun a ha => by rw [hZa y a ha]; exact hy a ha
      have := runLayer_ztGates ψ _ hy'
      change _ = ψ (ztZ d n (ztZ d n y)) at this
      rw [this, ztZ_ztZ]
    · have hy' : ¬ ∀ a ∈ ztA d n, ztZ d n y a = false := fun h => hy fun a ha => by
        rw [← hZa y a ha]; exact h a ha
      rw [hsupp _ hy', hdirty y hy]
  rw [h1]
  -- split the two branches
  have h2 : ∀ y, (if ztZ d n y (outW d n) = true then ‖ψ y‖ ^ 2 else 0) =
      (1 / 2 : ℝ) * ((if y (outW d n) = true then 1 else 0) * ‖Φ false F (outC d n hd y, μ)‖ ^ 2 +
        (if ztZ d n y (outW d n) = true then 1 else 0) * ‖Φ true B (y, μ)‖ ^ 2) := by
    intro y
    have hnorm : ‖ψ y‖ ^ 2 = (1 / 2 : ℝ) * (‖Φ false F (outC d n hd y, μ)‖ ^ 2 + ‖Φ true B (y, μ)‖ ^ 2) := by
      rw [hψy, norm_mul, mul_pow, norm_inv]
      rw [norm_sq_add_of_mul]
      · congr 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
          Real.sq_sqrt (by norm_num)]
        norm_num
      · cases hc : y (coinW d n)
        · right; exact Φ_coin_ne (by rw [hc]; decide) μ
        · left; exact Φ_coin_ne (by rw [hCc, hc]; decide) μ
    rw [hnorm]
    cases hc : y (coinW d n)
    · have hB : Φ true B (y, μ) = 0 := Φ_coin_ne (by rw [hc]; decide) μ
      have hZo : ztZ d n y (outW d n) = y (outW d n) := by
        simp only [ztZ, ztFun, Function.update_self, hc, Bool.false_and, Bool.xor_false]
      rw [hB, hZo]
      split_ifs <;> simp
    · have hF : Φ false F (outC d n hd y, μ) = 0 := Φ_coin_ne (by rw [hCc, hc]; decide) μ
      rw [hF]
      split_ifs <;> simp
  rw [Finset.sum_congr rfl fun y _ => h2 y, ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 2
  · -- the forward branch
    rw [← sum_invol (outC_outC hd)]
    simp only [outC_outC]
    rw [sum_Φ false F μ (fun y => if outC d n hd y (outW d n) = true then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun β _ => ?_
    have hco : outC d n hd (asm d n false x β) (outW d n) = x ⟨d.out, out_lt_W hd⟩ := by
      simp only [outC, cnotFun, Function.update_self, (ctlOK_asm false x β).2.1, Bool.false_xor]
      simp [asm, outD, workEmb, out_lt_W hd]
    have hob : outBit d x ↔ x ⟨d.out, out_lt_W hd⟩ = true :=
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨out_lt_W hd, h⟩⟩
    simp only [hco, hob]
    split_ifs <;> simp
  · -- the backward branch
    rw [sum_Φ true B μ (fun y => if ztZ d n y (outW d n) = true then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun β _ => ?_
    have hzo : ztZ d n (asm d n true x β) (outW d n) = true ↔ Zero0 d x := by
      simp only [ztZ, ztFun, Function.update_self, (ctlOK_asm true x β).2.1, (ctlOK_asm true x β).1,
        Bool.false_xor, Bool.true_and]
      rw [zero0_iff_all, workPart_asm]
    simp only [hzo]
    split_ifs <;> simp

end ShiQIP
