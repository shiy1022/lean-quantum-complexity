/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Pair.Valid
import QIP.Circuit.Controlled
import QIP.PureRun
import QIP.Prefix
import QIP.Bell.Run

/-!
# Q27 — clean provers

A message to the prover is never touched by the verifier again (validity). An isometric prover
can therefore keep each received register in a fresh memory slot and return `|0⟩`, without
changing the acceptance probability (**`exists_clean`**). In the resulting runs every wire of an
earlier message to the prover reads `0`.

* `runLayer_comp`: a layer avoiding a wire set `D` commutes with any map on basis labels that
  only changes `D`, and with multiplication by functions of the `D`-part.
* `Valid.support_held`: the instructions of block `j` only touch wires held during block `j`.
-/

set_option linter.unusedSimpArgs false

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Layers avoiding a set of wires -/

section Locality

variable {n : ℕ} (D : Fin n → Prop)

theorem instr_apply_comp (g : Instr n) (hg : ∀ w ∈ g.support, ¬ D w)
    (f : Qubits n → Qubits n)
    (hf1 : ∀ y i b, ¬ D i → f (Function.update y i b) = Function.update (f y) i b)
    (hf2 : ∀ y i, ¬ D i → f y i = y i) (c : Qubits n → ℂ)
    (hc : ∀ y i b, ¬ D i → c (Function.update y i b) = c y) (ψ : QState n) :
    g.apply (fun y => c y * ψ (f y)) = fun y => c y * g.apply ψ (f y) := by
  funext y
  cases g with
  | h i | s i | t i | x i =>
    have hi : ¬ D i := hg i (by simp [Instr.support])
    simp only [Instr.apply, apply1, hc _ _ _ hi, hf1 _ _ _ hi, hf2 _ _ hi, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  | cnot i j hij =>
    have hi : ¬ D i := hg i (by simp [Instr.support])
    have hj : ¬ D j := hg j (by simp [Instr.support])
    simp only [Instr.apply, cnotState, hc _ _ _ hj, hf1 _ _ _ hj, hf2 _ _ hi, hf2 _ _ hj]

theorem runLayer_comp (f : Qubits n → Qubits n)
    (hf1 : ∀ y i b, ¬ D i → f (Function.update y i b) = Function.update (f y) i b)
    (hf2 : ∀ y i, ¬ D i → f y i = y i) (c : Qubits n → ℂ)
    (hc : ∀ y i b, ¬ D i → c (Function.update y i b) = c y) :
    ∀ (l : List (Instr n)), (∀ g ∈ l, ∀ w ∈ g.support, ¬ D w) → ∀ ψ : QState n,
      runLayer l (fun y => c y * ψ (f y)) = fun y => c y * runLayer l ψ (f y)
  | [], _, ψ => rfl
  | g :: l, hl, ψ => by
    rw [runLayer_cons, instr_apply_comp D g (hl g List.mem_cons_self) f hf1 hf2 c hc,
      runLayer_comp f hf1 hf2 c hc l (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))]
    rfl

end Locality

/-! ## Validity and held wires -/

theorem Desc.Valid.support_held {d : Desc} (hd : d.Valid) (j : ℕ) :
    ∀ g ∈ (d.blocks.getD j []).filterMap (Gate.toInstr? d.totalWires), ∀ w ∈ g.support,
      d.held j w = true := by
  intro g hg w hw
  obtain ⟨g₀, hg₀, he⟩ := List.mem_filterMap.mp hg
  have hok := blocksOkFrom_getD d.blocks 0 j hd.blocksOk g₀ hg₀
  rw [zero_add] at hok
  cases g₀ with
  | h a | s a | t a | x a =>
    simp only [Gate.toInstr?] at he
    split_ifs at he
    cases he
    simp only [Instr.support, Finset.mem_singleton] at hw
    subst hw
    simpa [Gate.okBool] using hok
  | cnot a b =>
    simp only [Gate.toInstr?] at he
    split_ifs at he
    cases he
    simp only [Instr.support, Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Gate.okBool, Bool.and_eq_true] at hok
    rcases hw with rfl | rfl
    · exact hok.1.1
    · exact hok.1.2

theorem inReg_unique {d : Desc} {i j : ℕ} {x : Fin d.totalWires} (hi : inReg d i x)
    (hj : inReg d j x) : i = j := by
  unfold inReg at hi hj
  rw [msgOffset_eq, msgWidth_eq] at hi hj
  have := segment_unique (segs d) hi.1 hi.2 hj.1 hj.2
  omega

/-- Message `j` goes to the prover. -/
def toProverAt (d : Desc) (j : ℕ) : Prop :=
  (d.msgs.map Message.dir).getD j .toVerifier = .toProver

instance (d : Desc) (j : ℕ) : Decidable (toProverAt d j) := by unfold toProverAt; infer_instance

theorem lt_of_toProverAt {d : Desc} {j : ℕ} (h : toProverAt d j) : j < d.numMsgs := by
  by_contra hc
  unfold toProverAt at h
  rw [List.getD_eq_default _ _ (by simp [Desc.numMsgs] at hc ⊢; omega)] at h
  exact Dir.noConfusion h

/-- **A message sent to the prover is never held again.** -/
theorem not_held_of_dead {d : Desc} {j k : ℕ} (hjk : j < k) (hp : toProverAt d j)
    {x : Fin d.totalWires} (hx : inReg d j x) : d.held k x = false := by
  rw [Bool.eq_false_iff, ne_eq, held_iff]
  rintro (h | ⟨i, hi, hdir⟩)
  · have : d.priv ≤ d.msgOffset j := by simp [Desc.msgOffset]
    exact absurd hx.1 (by omega)
  · obtain rfl := inReg_unique hi hx
    unfold toProverAt at hp
    rw [hp] at hdir
    simp [dirOk] at hdir
    omega

/-! ## The clean prover -/

section Clean

variable {d : Desc} (T : IsoStrategy (Reg d) (Reg d) d.numMsgs)

variable (d) in
/-- One storage slot per message register. -/
abbrev Slots : Type := (j : Fin d.numMsgs) → Reg d j

variable (d) in
/-- Empty slots. -/
def zeroSlots : Slots d := fun _ _ => false

/-- A turn that leaves the slots alone. -/
noncomputable def keepV (k : ℕ) :
    Matrix (Reg d k × (T.M (k + 1) × Slots d)) (Reg d k × (T.M k × Slots d)) ℂ :=
  Matrix.of fun p q => T.V k (p.1, p.2.1) (q.1, q.2.1) * (if p.2.2 = q.2.2 then 1 else 0)

/-- A turn on a message to the prover: run `T`, then swap the register with slot `k`. -/
noncomputable def swapV (k : ℕ) (hk : k < d.numMsgs) :
    Matrix (Reg d k × (T.M (k + 1) × Slots d)) (Reg d k × (T.M k × Slots d)) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.2.2 ⟨k, hk⟩ ∧ ∀ i, i ≠ ⟨k, hk⟩ → p.2.2 i = q.2.2 i then
      T.V k (p.2.2 ⟨k, hk⟩, p.2.1) (q.1, q.2.1) else 0

theorem V_iso_apply {k : ℕ} (hk : k < d.numMsgs) (a b : Reg d k × T.M k) :
    ∑ g, ∑ μ, star (T.V k (g, μ) a) * T.V k (g, μ) b = if a = b then 1 else 0 := by
  have := congrArg (fun M => M a b) (T.V_iso k hk)
  simpa [mul_apply, Fintype.sum_prod_type, one_apply] using this

theorem star_ite' {p : Prop} [Decidable p] (a b : ℂ) :
    star (if p then a else b) = if p then star a else star b := by
  split_ifs <;> rfl

theorem keepV_iso {k : ℕ} (hk : k < d.numMsgs) : (keepV T k)ᴴ * keepV T k = 1 := by
  ext ⟨g, μ, s⟩ ⟨g', μ', s'⟩
  simp only [mul_apply, conjTranspose_apply, keepV, of_apply, Fintype.sum_prod_type, one_apply,
    star_mul', star_ite', star_one, star_zero]
  have : ∀ (x : Reg d k) (ν : T.M (k + 1)), ∑ t : Slots d,
      star (T.V k (x, ν) (g, μ)) * (if t = s then 1 else 0) *
        (T.V k (x, ν) (g', μ') * (if t = s' then 1 else 0)) =
      if s = s' then star (T.V k (x, ν) (g, μ)) * T.V k (x, ν) (g', μ') else 0 := by
    intro x ν
    rw [Finset.sum_eq_single s]
    · split_ifs <;> simp_all
    · intro t _ ht; simp [ht]
    · simp
  simp only [this]
  by_cases hs : s = s'
  · subst hs
    simp only [if_true]
    rw [V_iso_apply T hk (g, μ) (g', μ')]
    simp [Prod.mk.injEq, and_assoc]
  · simp [hs]

theorem sum_slots (k : Fin d.numMsgs) (s : Slots d) (F : Reg d k → ℂ) :
    ∑ t : Slots d, (if ∀ i, i ≠ k → t i = s i then F (t k) else 0) = ∑ h, F h := by
  rw [← (Equiv.piSplitAt k (fun j => Reg d j)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_eq_single (fun i : {j // j ≠ k} => s i.1 : (i : {j // j ≠ k}) → Reg d i.1)]
  · rw [if_pos]
    · simp [Equiv.piSplitAt_symm_apply]
    · intro i hi
      simp [Equiv.piSplitAt_symm_apply, hi]
  · intro r _ hr
    rw [if_neg]
    intro hc
    apply hr
    funext i
    have := hc i.1 i.2
    simpa [Equiv.piSplitAt_symm_apply, i.2] using this
  · simp

theorem swapV_iso {k : ℕ} (hk : k < d.numMsgs) : (swapV T k hk)ᴴ * swapV T k hk = 1 := by
  ext ⟨g, μ, s⟩ ⟨g', μ', s'⟩
  simp only [mul_apply, conjTranspose_apply, swapV, of_apply, Fintype.sum_prod_type, one_apply]
  by_cases hs : s = s'
  · subst hs
    have key : ∀ (x : Reg d k) (ν : T.M (k + 1)), ∑ t : Slots d,
        star (if x = s ⟨k, hk⟩ ∧ ∀ i, i ≠ ⟨k, hk⟩ → t i = s i then T.V k (t ⟨k, hk⟩, ν) (g, μ)
          else 0) *
        (if x = s ⟨k, hk⟩ ∧ ∀ i, i ≠ ⟨k, hk⟩ → t i = s i then T.V k (t ⟨k, hk⟩, ν) (g', μ')
          else 0) =
        if x = s ⟨k, hk⟩ then ∑ h : Reg d k, star (T.V k (h, ν) (g, μ)) * T.V k (h, ν) (g', μ')
          else 0 := by
      intro x ν
      split_ifs with hx
      · rw [← sum_slots ⟨k, hk⟩ s]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases ht : ∀ i, i ≠ ⟨k, hk⟩ → t i = s i
        · rw [if_pos ⟨hx, ht⟩, if_pos ⟨hx, ht⟩, if_pos ht]
        · rw [if_neg (fun h => ht h.2), if_neg ht]; simp
      · simp [hx]
    simp only [key]
    rw [Finset.sum_eq_single (s ⟨k, hk⟩)]
    · simp only [if_true]
      rw [Finset.sum_comm, V_iso_apply T hk (g, μ) (g', μ')]
      simp [Prod.mk.injEq, and_assoc]
    · intro x _ hx; simp [hx]
    · simp
  · rw [if_neg (by simp [hs])]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun ν _ =>
      Finset.sum_eq_zero fun t _ => ?_
    by_cases h1 : x = s ⟨k, hk⟩ ∧ ∀ i, i ≠ ⟨k, hk⟩ → t i = s i
    · by_cases h2 : x = s' ⟨k, hk⟩ ∧ ∀ i, i ≠ ⟨k, hk⟩ → t i = s' i
      · exfalso; apply hs
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi; exact h1.1.symm.trans h2.1
        · exact (h1.2 i hi).symm.trans (h2.2 i hi)
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, star_zero, zero_mul]

/-- The turns of the clean prover. -/
noncomputable def cleanV (k : ℕ) :
    Matrix (Reg d k × (T.M (k + 1) × Slots d)) (Reg d k × (T.M k × Slots d)) ℂ :=
  if h : k < d.numMsgs ∧ toProverAt d k then swapV T k h.1 else keepV T k

/-- **The clean prover**: `T` with one storage slot per register. -/
@[reducible] noncomputable def cleanT : IsoStrategy (Reg d) (Reg d) d.numMsgs where
  M k := T.M k × Slots d
  init p := T.init p.1 * (if p.2 = zeroSlots d then 1 else 0)
  init_density := by
    have h := kronecker_pureState T.init (fun t : Slots d => if t = zeroSlots d then (1 : ℂ) else 0)
    rw [← h]
    exact T.init_density.kronecker (by rw [isDensity_pure_iff]; simp [apply_ite])
  V := cleanV T
  V_iso k hk := by
    unfold cleanV
    split_ifs with h
    · exact swapV_iso T h.1
    · exact keepV_iso T hk

/-! ## Merging the slots back -/

attribute [local instance] Classical.propDecidable

variable (d) in
/-- Wire `w` lies in a message to the prover sent before block `k`. -/
def DW (k : ℕ) (w : Fin d.totalWires) : Prop := ∃ j, j < k ∧ toProverAt d j ∧ inReg d j w

/-- Put the slot contents back on the dead wires. -/
noncomputable def merge (k : ℕ) (y : Qubits d.totalWires) (s : Slots d) : Qubits d.totalWires :=
  fun w => if h : DW d k w then
    s ⟨h.choose, lt_of_toProverAt h.choose_spec.2.1⟩ ⟨w, h.choose_spec.2.2⟩ else y w

/-- The clean prover's states are supported here. -/
def good (k : ℕ) (y : Qubits d.totalWires) (s : Slots d) : Prop :=
  (∀ w, DW d k w → y w = false) ∧ ∀ i : Fin d.numMsgs, ¬ ((i : ℕ) < k ∧ toProverAt d i) →
    s i = fun _ => false

theorem slot_congr (s : Slots d) {j₁ j₂ : ℕ} (e : j₁ = j₂) (h₁ : j₁ < d.numMsgs)
    (h₂ : j₂ < d.numMsgs) {w : Fin d.totalWires} (hw₁ : inReg d j₁ w) (hw₂ : inReg d j₂ w) :
    s ⟨j₁, h₁⟩ ⟨w, hw₁⟩ = s ⟨j₂, h₂⟩ ⟨w, hw₂⟩ := by
  subst e; rfl

theorem merge_of_not {k : ℕ} {w : Fin d.totalWires} (h : ¬ DW d k w) (y : Qubits d.totalWires)
    (s : Slots d) : merge k y s w = y w := by
  rw [merge, dif_neg h]

theorem merge_of_mem {k j : ℕ} {w : Fin d.totalWires} (hj : j < k) (hp : toProverAt d j)
    (hw : inReg d j w) (y : Qubits d.totalWires) (s : Slots d) :
    merge k y s w = s ⟨j, lt_of_toProverAt hp⟩ ⟨w, hw⟩ := by
  have h : DW d k w := ⟨j, hj, hp, hw⟩
  rw [merge, dif_pos h]
  exact slot_congr s (inReg_unique h.choose_spec.2.2 hw) _ _ _ _

theorem not_DW_of_inReg {k : ℕ} {w : Fin d.totalWires} (hw : inReg d k w) : ¬ DW d k w := by
  rintro ⟨j, hj, _, hw'⟩
  have := inReg_unique hw hw'
  omega

theorem DW_succ {k : ℕ} {w : Fin d.totalWires} :
    DW d (k + 1) w ↔ DW d k w ∨ (toProverAt d k ∧ inReg d k w) := by
  constructor
  · rintro ⟨j, hj, hp, hw⟩
    by_cases hjk : j < k
    · exact Or.inl ⟨j, hjk, hp, hw⟩
    · have : j = k := by omega
      subst this; exact Or.inr ⟨hp, hw⟩
  · rintro (⟨j, hj, hp, hw⟩ | ⟨hp, hw⟩)
    · exact ⟨j, by omega, hp, hw⟩
    · exact ⟨k, by omega, hp, hw⟩

theorem regSet_snd (k : ℕ) (y : Qubits d.totalWires) (x : Reg d k) :
    (wireSplitE d k (PrefixData.regSet d k y x)).2 = x := by
  simp [PrefixData.regSet]

theorem regSet_regSet (k : ℕ) (y : Qubits d.totalWires) (a x : Reg d k) :
    PrefixData.regSet d k (PrefixData.regSet d k y a) x = PrefixData.regSet d k y x := by
  simp [PrefixData.regSet]

theorem good_regSet {k : ℕ} (y : Qubits d.totalWires) (x : Reg d k) (s : Slots d) :
    good k (PrefixData.regSet d k y x) s ↔ good k y s := by
  unfold good
  refine and_congr (forall_congr' fun w => forall_congr' fun hw => ?_) Iff.rfl
  rw [PrefixData.regSet_apply, dif_neg (fun h => not_DW_of_inReg h hw)]

theorem merge_regSet {k : ℕ} (y : Qubits d.totalWires) (x : Reg d k) (s : Slots d) :
    merge k (PrefixData.regSet d k y x) s = PrefixData.regSet d k (merge k y s) x := by
  funext w
  rw [PrefixData.regSet_apply]
  by_cases hw : inReg d k w
  · rw [dif_pos hw, merge_of_not (not_DW_of_inReg hw), PrefixData.regSet_apply, dif_pos hw]
  · rw [dif_neg hw]
    by_cases hD : DW d k w
    · obtain ⟨j, hj, hp, hjw⟩ := hD
      rw [merge_of_mem hj hp hjw, merge_of_mem hj hp hjw]
    · rw [merge_of_not hD, merge_of_not hD, PrefixData.regSet_apply, dif_neg hw]

theorem wireSplitE_merge {k : ℕ} (y : Qubits d.totalWires) (s : Slots d) :
    (wireSplitE d k (merge k y s)).2 = (wireSplitE d k y).2 := by
  funext r
  exact merge_of_not (not_DW_of_inReg r.2) y s

theorem good_succ_keep {k : ℕ} (hp : ¬ toProverAt d k) (y : Qubits d.totalWires) (s : Slots d) :
    good (k + 1) y s ↔ good k y s := by
  unfold good
  refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun i => ?_)
  · rw [DW_succ]; simp [hp]
  · constructor
    · intro h hi; exact h fun ⟨h1, h2⟩ => hi ⟨by
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · exact h1
        · exact absurd (h1 ▸ h2) hp, h2⟩
    · intro h hi; exact h fun ⟨h1, h2⟩ => hi ⟨by omega, h2⟩

theorem merge_succ_keep {k : ℕ} (hp : ¬ toProverAt d k) (y : Qubits d.totalWires) (s : Slots d) :
    merge (k + 1) y s = merge k y s := by
  funext w
  by_cases hD : DW d k w
  · obtain ⟨j, hj, hpj, hjw⟩ := hD
    rw [merge_of_mem (by omega) hpj hjw, merge_of_mem hj hpj hjw]
  · rw [merge_of_not hD, merge_of_not (by rw [DW_succ]; simp [hD, hp])]

theorem merge_succ_swap {k : ℕ} (hk : k < d.numMsgs) (hp : toProverAt d k)
    (y : Qubits d.totalWires) (s : Slots d) :
    merge (k + 1) y s = PrefixData.regSet d k (merge k y s) (s ⟨k, hk⟩) := by
  funext w
  rw [PrefixData.regSet_apply]
  by_cases hw : inReg d k w
  · rw [dif_pos hw, merge_of_mem (by omega) hp hw]
  · rw [dif_neg hw]
    by_cases hD : DW d k w
    · obtain ⟨j, hj, hpj, hjw⟩ := hD
      rw [merge_of_mem (by omega) hpj hjw, merge_of_mem hj hpj hjw]
    · rw [merge_of_not hD, merge_of_not (by rw [DW_succ]; simp [hD, hw])]

theorem merge_update_slot {k : ℕ} (hk : k < d.numMsgs) (y : Qubits d.totalWires) (s : Slots d)
    (g : Reg d k) : merge k y (Function.update s ⟨k, hk⟩ g) = merge k y s := by
  funext w
  by_cases hD : DW d k w
  · obtain ⟨j, hj, hpj, hjw⟩ := hD
    rw [merge_of_mem hj hpj hjw, merge_of_mem hj hpj hjw,
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp at this; omega)]
  · rw [merge_of_not hD, merge_of_not hD]

theorem good_swap {k : ℕ} (hk : k < d.numMsgs) (hp : toProverAt d k) (y : Qubits d.totalWires)
    (x : Reg d k) (s : Slots d) :
    good k (PrefixData.regSet d k y x) (Function.update s ⟨k, hk⟩ (wireSplitE d k y).2) ↔
      good (k + 1) y s := by
  rw [good_regSet]
  unfold good
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun w hw => ?_, fun i hi => ?_⟩
    · rcases DW_succ.mp hw with hw | ⟨_, hw⟩
      · exact h1 w hw
      · have := congrFun (h2 ⟨k, hk⟩ (by simp)) ⟨w, hw⟩
        rw [Function.update_self] at this
        exact this
    · have hik : i ≠ ⟨k, hk⟩ := fun e => by subst e; exact hi ⟨Nat.lt_succ_self k, hp⟩
      have := h2 i (fun ⟨a, b⟩ => hi ⟨by omega, b⟩)
      rwa [Function.update_of_ne hik] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun w hw => h1 w (DW_succ.mpr (Or.inl hw)), fun i hi => ?_⟩
    by_cases hik : i = ⟨k, hk⟩
    · subst hik
      rw [Function.update_self]
      funext r
      exact h1 r.1 (DW_succ.mpr (Or.inr ⟨hp, r.2⟩))
    · rw [Function.update_of_ne hik]
      refine h2 i fun ⟨a, b⟩ => hi ⟨?_, b⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp a with a | a
      · exact a
      · exact absurd (Fin.ext a) hik

/-- **A turn of the clean prover.** -/
theorem turn_clean (k : ℕ) (hk : k < d.numMsgs)
    (v : Qubits d.totalWires × (cleanT T).M k → ℂ) (v₀ : Qubits d.totalWires × T.M k → ℂ)
    (hv : ∀ y μ s, v (y, (μ, s)) = (if good k y s then 1 else 0) * v₀ (merge k y s, μ))
    (y : Qubits d.totalWires) (μ : T.M (k + 1)) (s : Slots d) :
    turnVec (cleanT T) k v (y, (μ, s)) =
      (if good (k + 1) y s then 1 else 0) * turnVec T k v₀ (merge (k + 1) y s, μ) := by
  rw [PrefixData.turnVec_apply, PrefixData.turnVec_apply]
  simp only [Fintype.sum_prod_type]
  change ∑ x, ∑ ν, ∑ t, cleanV T k _ _ * _ = _
  by_cases hp : k < d.numMsgs ∧ toProverAt d k
  · rw [cleanV, dif_pos hp, merge_succ_swap hk hp.2, regSet_snd]
    simp only [swapV, of_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_eq_single (Function.update s ⟨k, hk⟩ (wireSplitE d k y).2)]
    · rw [if_pos ⟨by rw [Function.update_self], fun i hi => by rw [Function.update_of_ne hi]⟩,
        hv, good_swap hk hp.2, merge_regSet, merge_update_slot, regSet_regSet]
      ring
    · intro t _ ht
      rw [if_neg, zero_mul]
      rintro ⟨h1, h2⟩
      apply ht
      funext i
      by_cases hi : i = ⟨k, hk⟩
      · subst hi; rw [Function.update_self]; exact h1.symm
      · rw [Function.update_of_ne hi]; exact (h2 i hi).symm
    · simp
  · have hp' : ¬ toProverAt d k := fun h => hp ⟨hk, h⟩
    rw [cleanV, dif_neg hp, merge_succ_keep hp', good_succ_keep hp', wireSplitE_merge]
    simp only [keepV, of_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_eq_single s]
    · rw [if_pos rfl, hv, good_regSet, merge_regSet]
      ring
    · intro t _ ht
      rw [if_neg (Ne.symm ht)]; ring
    · simp

theorem kronOne_mulVec_apply {α M : Type} [Fintype α] [Fintype M] [DecidableEq M]
    (A : Matrix α α ℂ) (v : α × M → ℂ) (y : α) (μ : M) :
    ((A ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ v) (y, μ) = (A *ᵥ fun y' => v (y', μ)) y := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem merge_update {k : ℕ} {i : Fin d.totalWires} (hi : ¬ DW d k i) (y : Qubits d.totalWires)
    (b : Bool) (s : Slots d) :
    merge k (Function.update y i b) s = Function.update (merge k y s) i b := by
  funext w
  by_cases hwi : w = i
  · subst hwi; rw [merge_of_not hi, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hwi]
    by_cases hD : DW d k w
    · obtain ⟨j, hj, hpj, hjw⟩ := hD
      rw [merge_of_mem hj hpj hjw, merge_of_mem hj hpj hjw]
    · rw [merge_of_not hD, merge_of_not hD, Function.update_of_ne hwi]

theorem good_update {k : ℕ} {i : Fin d.totalWires} (hi : ¬ DW d k i) (y : Qubits d.totalWires)
    (b : Bool) (s : Slots d) : good k (Function.update y i b) s ↔ good k y s := by
  unfold good
  refine and_congr (forall_congr' fun w => forall_congr' fun hw => ?_) Iff.rfl
  rw [Function.update_of_ne (fun e : w = i => hi (by rw [← e]; exact hw))]

/-- **A verifier block on the clean prover's run.** -/
theorem block_clean (hd : d.Valid) (k : ℕ) (ψ : Qubits d.totalWires × T.M k → ℂ)
    (ψ' : Qubits d.totalWires × (cleanT T).M k → ℂ)
    (h : ∀ y μ s, ψ' (y, (μ, s)) = (if good k y s then 1 else 0) * ψ (merge k y s, μ))
    (y : Qubits d.totalWires) (μ : T.M k) (s : Slots d) :
    ((blockMat d k ⊗ₖ (1 : Matrix ((cleanT T).M k) ((cleanT T).M k) ℂ)) *ᵥ ψ') (y, (μ, s)) =
      (if good k y s then 1 else 0) *
        ((blockMat d k ⊗ₖ (1 : Matrix (T.M k) (T.M k) ℂ)) *ᵥ ψ) (merge k y s, μ) := by
  rw [kronOne_mulVec_apply, kronOne_mulVec_apply, blockMat, layerMat_mulVec, layerMat_mulVec]
  have hψ' : (fun y' => ψ' (y', (μ, s))) = fun y' =>
      (fun y'' => if good k y'' s then (1 : ℂ) else 0) y' *
        (fun y'' => ψ (y'', μ)) ((fun y'' => merge k y'' s) y') := funext fun y' => h y' μ s
  have hl : ∀ g ∈ (d.blocks.getD k []).filterMap (Gate.toInstr? d.totalWires),
      ∀ w ∈ g.support, ¬ DW d k w := by
    intro g hg w hw hD
    obtain ⟨j, hj, hp, hjw⟩ := hD
    have h1 := hd.support_held k g hg w hw
    rw [not_held_of_dead hj hp hjw] at h1
    exact Bool.noConfusion h1
  have key := runLayer_comp (DW d k) (fun y'' => merge k y'' s)
    (fun y i b hi => merge_update hi y b s) (fun y i hi => merge_of_not hi y s)
    (fun y'' => if good k y'' s then (1 : ℂ) else 0)
    (fun y i b hi => by simp only [good_update hi]) _ hl (fun y'' => ψ (y'', μ))
  rw [hψ']
  exact congrFun key y

theorem good_zero (y : Qubits d.totalWires) (s : Slots d) : good 0 y s ↔ s = zeroSlots d := by
  unfold good
  constructor
  · rintro ⟨_, h⟩; funext i; exact h i (fun ⟨h1, _⟩ => by omega)
  · rintro rfl; exact ⟨fun w ⟨j, hj, _⟩ => by omega, fun i _ => rfl⟩

theorem merge_zero (y : Qubits d.totalWires) (s : Slots d) : merge 0 y s = y :=
  funext fun w => merge_of_not (fun ⟨j, hj, _⟩ => by omega) y s

/-- **The clean run is the original run with the slots put back.** -/
theorem pureRun_clean (hd : d.Valid) : ∀ k ≤ d.numMsgs, ∀ y μ s,
    pureRun (cleanT T) k (y, (μ, s)) =
      (if good k y s then 1 else 0) * pureRun T k (merge k y s, μ)
  | 0, _, y, μ, s => by
    rw [pureRun, pureRun]
    refine block_clean T hd 0 _ _ (fun y μ s => ?_) y μ s
    change zeroVec _ y * (T.init μ * (if s = zeroSlots d then 1 else 0)) = _
    rw [merge_zero]
    by_cases hs : s = zeroSlots d
    · rw [if_pos hs, if_pos ((good_zero y s).mpr hs)]; ring
    · rw [if_neg hs, if_neg (fun h => hs ((good_zero y s).mp h))]; ring
  | k + 1, hk, y, μ, s => by
    rw [pureRun, pureRun]
    exact block_clean T hd (k + 1) _ _ (turn_clean T k (by omega) _ _
      (pureRun_clean hd k (by omega))) y μ s

variable (k : ℕ) in
/-- Clear the dead wires. -/
noncomputable def unmerge (y : Qubits d.totalWires) : Qubits d.totalWires :=
  fun w => if DW d k w then false else y w

variable (k : ℕ) in
/-- Read the dead registers into the slots. -/
noncomputable def slotsOf (y : Qubits d.totalWires) : Slots d :=
  fun i => if (i : ℕ) < k ∧ toProverAt d i then fun r => y r.1 else fun _ => false

theorem sum_good_merge (k : ℕ) (G : Qubits d.totalWires → ℝ) :
    ∑ y, ∑ s, (if good k y s then G (merge k y s) else 0) = ∑ y, G y := by
  rw [← Fintype.sum_prod_type' (f := fun y s => if good k y s then G (merge k y s) else 0),
    ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun p => merge k p.1 p.2) (fun y => (unmerge k y, slotsOf k y))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro y _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun w hw => by simp [unmerge, hw], fun i hi => ?_⟩
    simp only [slotsOf, if_neg hi]
  · rintro ⟨y, s⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine Prod.ext (funext fun w => ?_) (funext fun i => ?_)
    · change (if DW d k w then false else merge k y s w) = y w
      split_ifs with hw
      · exact (hp.1 w hw).symm
      · exact merge_of_not hw y s
    · change (if (i : ℕ) < k ∧ toProverAt d i then fun r => merge k y s r.1 else fun _ => false) = s i
      split_ifs with hi
      · funext r
        exact merge_of_mem hi.1 hi.2 r.2 y s
      · exact (hp.2 i hi).symm
  · intro y _
    funext w
    by_cases hw : DW d k w
    · obtain ⟨j, hj, hp, hjw⟩ := hw
      rw [merge_of_mem hj hp hjw]
      change (if ((⟨j, lt_of_toProverAt hp⟩ : Fin d.numMsgs) : ℕ) < k ∧ toProverAt d j then
        fun r : {x // inReg d j x} => y r.1 else fun _ => false) ⟨w, hjw⟩ = y w
      rw [if_pos ⟨hj, hp⟩]
    · rw [merge_of_not hw]
      change (if DW d k w then false else y w) = y w
      rw [if_neg hw]

/-- **Cleaning does not change the acceptance probability.** -/
theorem accept_clean (hd : d.Valid) : accept (cleanT T).toOp = accept T.toOp := by
  rw [accept_pureRun, accept_pureRun, accept_expect, accept_expect]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun y μ => if outBit d y then
    ‖pureRun T d.numMsgs (y, μ)‖ ^ 2 else 0)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← sum_good_merge d.numMsgs (fun y => if outBit d y then ‖pureRun T d.numMsgs (y, μ)‖ ^ 2 else 0)]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s _ => ?_
  rw [pureRun_clean T hd _ le_rfl]
  have hout : outBit d (merge d.numMsgs y s) ↔ outBit d y := by
    constructor
    · rintro ⟨h, e⟩
      refine ⟨h, ?_⟩
      rwa [merge_of_not] at e
      rintro ⟨j, _, _, hjw⟩
      have : d.priv ≤ d.msgOffset j := by simp [Desc.msgOffset]
      have := hjw.1
      have := hd.out_lt
      simp only at *; omega
    · rintro ⟨h, e⟩
      refine ⟨h, ?_⟩
      rw [merge_of_not]
      · exact e
      rintro ⟨j, _, _, hjw⟩
      have : d.priv ≤ d.msgOffset j := by simp [Desc.msgOffset]
      have := hjw.1
      have := hd.out_lt
      simp only at *; omega
  by_cases hg : good d.numMsgs y s
  · simp only [if_pos hg, one_mul]
    by_cases ho : outBit d y
    · rw [if_pos ho, if_pos (hout.mpr ho)]
    · rw [if_neg ho, if_neg (fun h => ho (hout.mp h))]
  · simp [hg]

/-- **Every isometric prover of a valid description has a clean version**: same acceptance,
and every wire of a message to the prover reads `0` at the end. -/
theorem exists_clean (hd : d.Valid) :
    ∃ T' : IsoStrategy (Reg d) (Reg d) d.numMsgs, accept T'.toOp = accept T.toOp ∧
      ∀ (j : ℕ) (w : Fin d.totalWires), toProverAt d j → inReg d j w →
        ∀ y μ, y w = true → pureRun T' d.numMsgs (y, μ) = 0 := by
  refine ⟨cleanT T, accept_clean T hd, fun j w hp hw y μ hy => ?_⟩
  obtain ⟨μ, s⟩ := μ
  rw [pureRun_clean T hd _ le_rfl, if_neg, zero_mul]
  intro hg
  rw [hg.1 w ⟨j, lt_of_toProverAt hp, hp, hw⟩] at hy
  exact Bool.noConfusion hy

end Clean

end ShiQIP
