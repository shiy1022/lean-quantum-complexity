/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Pair.Desc
import QIP.ValidGates

/-!
# Q25 — validity of the paired description

**`pairDesc_valid`**: if `d₁` and `d₂` are valid and have the same message directions, then
`pairDesc d₁ d₂` is valid. Every relabelled gate of copy `c` touches only wires held by the
paired verifier, because held message wires of a copy map to held wires of the same message
(`held_pos₁`, `held_pos₂`). The final Toffoli acts on private wires.
-/

namespace ShiQIP

open ShiShallow

/-- The holding condition of a message register during block `j`. -/
def dirOk : Dir → ℕ → ℕ → Bool
  | .toVerifier, k, j => decide (k < j)
  | .toProver, k, j => decide (j ≤ k)

theorem msgHeld_iff (j w : ℕ) : ∀ (ms : List Message) (k off : ℕ),
    msgHeld j w ms k off = true ↔ ∃ i, off + psum (ms.map Message.width) i ≤ w ∧
      w < off + psum (ms.map Message.width) i + (ms.map Message.width).getD i 0 ∧
        dirOk ((ms.map Message.dir).getD i .toVerifier) (k + i) j = true
  | [], k, off => by
    simp only [msgHeld, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i h1 h2
    simp [psum] at h1 h2
    omega
  | m :: ms, k, off => by
    rw [msgHeld, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, msgHeld_iff j w ms]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨i, h1, h2, h3⟩)
      · refine ⟨0, by simpa using h1, by simpa using h2, ?_⟩
        cases hd : m.dir <;> simp [hd, dirOk] at h3 ⊢ <;> exact h3
      · refine ⟨i + 1, ?_, ?_, ?_⟩
        · simp only [List.map_cons, psum_cons_succ]; omega
        · simp only [List.map_cons, psum_cons_succ, List.getD_cons_succ]; omega
        · simpa [Nat.add_assoc, Nat.add_comm 1] using h3
    · rintro ⟨i, h1, h2, h3⟩
      cases i with
      | zero =>
        left
        simp only [List.map_cons, psum_zero, List.getD_cons_zero, add_zero] at h1 h2 h3
        refine ⟨⟨h1, h2⟩, ?_⟩
        cases hd : m.dir <;> simp [hd, dirOk] at h3 ⊢ <;> exact h3
      | succ i =>
        right
        simp only [List.map_cons, psum_cons_succ, List.getD_cons_succ] at h1 h2 h3
        refine ⟨i, by omega, by omega, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm 1] using h3

/-- **Held wires of a description**: private wires and wires of messages currently held. -/
theorem held_iff (d : Desc) (j : ℕ) (x : Fin d.totalWires) :
    d.held j x = true ↔ (x : ℕ) < d.priv ∨
      ∃ i, inReg d i x ∧ dirOk ((d.msgs.map Message.dir).getD i .toVerifier) i j = true := by
  rw [Desc.held, Bool.or_eq_true, decide_eq_true_eq, msgHeld_iff]
  apply or_congr Iff.rfl
  apply exists_congr fun i => ?_
  unfold inReg
  rw [msgOffset_eq, msgWidth_eq]
  simp only [segs, psum_cons_succ, List.getD_cons_succ, zero_add, and_assoc]

variable {d₁ d₂ : Desc}

theorem pos₁_priv {x : ℕ} (hx : x < d₁.priv) : pos₁ d₁ d₂ x = 1 + x := by
  rw [pos₁_of_seg (i := 0) (by simp) (by simpa [segs] using hx)]
  simp

theorem pos₂_priv {y : ℕ} (hy : y < d₂.priv) : pos₂ d₁ d₂ y = 1 + d₁.priv + y := by
  rw [pos₂_of_seg (i := 0) (by simp) (by simpa [segs] using hy)]
  simp [segs, zw]

theorem dirs_pairDesc (hlen : d₁.numMsgs = d₂.numMsgs) :
    (pairDesc d₁ d₂).msgs.map Message.dir = d₁.msgs.map Message.dir :=
  pairMsgs_dirs _ _ hlen

theorem held_pos₁ (hlen : d₁.numMsgs = d₂.numMsgs) {j : ℕ} {x : Fin d₁.totalWires}
    (h : d₁.held j x = true) : (pairDesc d₁ d₂).held j (emb₁ d₁ d₂ hlen x) = true := by
  rw [held_iff] at h ⊢
  rcases h with h | ⟨i, hi, hd⟩
  · left
    change pos₁ d₁ d₂ x < 1 + d₁.priv + d₂.priv
    rw [pos₁_priv h]; omega
  · right
    refine ⟨i, (inReg_emb₁ hlen i x).mpr hi, ?_⟩
    rwa [dirs_pairDesc hlen]

theorem held_pos₂ (hlen : d₁.numMsgs = d₂.numMsgs)
    (hdir : d₁.msgs.map Message.dir = d₂.msgs.map Message.dir) {j : ℕ} {y : Fin d₂.totalWires}
    (h : d₂.held j y = true) : (pairDesc d₁ d₂).held j (emb₂ d₁ d₂ hlen y) = true := by
  rw [held_iff] at h ⊢
  rcases h with h | ⟨i, hi, hd⟩
  · left
    change pos₂ d₁ d₂ y < 1 + d₁.priv + d₂.priv
    rw [pos₂_priv h]; omega
  · right
    refine ⟨i, (inReg_emb₂ hlen i y).mpr hi, ?_⟩
    rwa [dirs_pairDesc hlen, hdir]

/-- Held wires of the paired description, on natural numbers. -/
theorem held_relabel₁ (hlen : d₁.numMsgs = d₂.numMsgs) {j w : ℕ} (h : d₁.held j w = true) :
    (pairDesc d₁ d₂).held j (pos₁ d₁ d₂ w) = true :=
  held_pos₁ hlen (x := ⟨w, Desc.held_lt h⟩) h

theorem held_relabel₂ (hlen : d₁.numMsgs = d₂.numMsgs)
    (hdir : d₁.msgs.map Message.dir = d₂.msgs.map Message.dir) {j w : ℕ}
    (h : d₂.held j w = true) : (pairDesc d₁ d₂).held j (pos₂ d₁ d₂ w) = true :=
  held_pos₂ hlen hdir (y := ⟨w, Desc.held_lt h⟩) h

theorem okBool_relabel₁ (hlen : d₁.numMsgs = d₂.numMsgs) {j : ℕ} {g : Gate}
    (hg : g.okBool (d₁.held j) = true) :
    (g.relabel (pos₁ d₁ d₂)).okBool ((pairDesc d₁ d₂).held j) = true := by
  cases g with
  | cnot a b =>
    simp only [Gate.okBool, Gate.relabel, Bool.and_eq_true, bne_iff_ne] at hg ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hg
    exact ⟨⟨held_relabel₁ hlen ha, held_relabel₁ hlen hb⟩,
      fun e => hab (pos₁_inj hlen (Desc.held_lt ha) (Desc.held_lt hb) e)⟩
  | _ i => exact held_relabel₁ hlen hg

theorem okBool_relabel₂ (hlen : d₁.numMsgs = d₂.numMsgs)
    (hdir : d₁.msgs.map Message.dir = d₂.msgs.map Message.dir) {j : ℕ} {g : Gate}
    (hg : g.okBool (d₂.held j) = true) :
    (g.relabel (pos₂ d₁ d₂)).okBool ((pairDesc d₁ d₂).held j) = true := by
  cases g with
  | cnot a b =>
    simp only [Gate.okBool, Gate.relabel, Bool.and_eq_true, bne_iff_ne] at hg ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hg
    exact ⟨⟨held_relabel₂ hlen hdir ha, held_relabel₂ hlen hdir hb⟩,
      fun e => hab (pos₂_inj hlen (Desc.held_lt ha) (Desc.held_lt hb) e)⟩
  | _ i => exact held_relabel₂ hlen hdir hg

/-- Every gate of the Toffoli template is well formed on three distinct good wires. -/
theorem okBool_toffoliGates {ok : ℕ → Bool} {a b c : ℕ} (ha : ok a = true) (hb : ok b = true)
    (hc : ok c = true) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ g ∈ toffoliGates a b c, g.okBool ok = true := by
  intro g hg
  simp only [toffoliGates, cczGates, tdgGates, List.replicate_succ, List.replicate_zero,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp [Gate.okBool, ha, hb, hc, hab, hac, hbc]

theorem blocksOkFrom_of {d : Desc} : ∀ (bs : List (List Gate)) (j₀ : ℕ),
    (∀ i, ∀ g ∈ bs.getD i [], g.okBool (d.held (j₀ + i)) = true) → d.blocksOkFrom bs j₀ = true
  | [], _, _ => rfl
  | b :: bs, j₀, h => by
    simp only [Desc.blocksOkFrom, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun g hg => by simpa using h 0 g (by simpa using hg), ?_⟩
    refine blocksOkFrom_of bs (j₀ + 1) fun i g hg => ?_
    have := h (i + 1) g (by simpa using hg)
    rwa [show j₀ + (i + 1) = j₀ + 1 + i by omega] at this

theorem alternates_congr : ∀ (ms ms' : List Message), ms.map Message.dir = ms'.map Message.dir →
    Desc.alternates ms = Desc.alternates ms'
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | a :: b :: ms, a' :: b' :: ms', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [Desc.alternates]
    rw [h.1, h.2.1, alternates_congr (b :: ms) (b' :: ms') (by simp [h.2.1, h.2.2])]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [_], _ :: _ :: _, h => by simp at h
  | _ :: _ :: _, [_], h => by simp at h

/-- **The paired description is valid.** -/
theorem pairDesc_valid (hlen : d₁.numMsgs = d₂.numMsgs)
    (hdir : d₁.msgs.map Message.dir = d₂.msgs.map Message.dir) (hd₁ : d₁.Valid)
    (hd₂ : d₂.Valid) : (pairDesc d₁ d₂).Valid := by
  unfold Desc.Valid Desc.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by simp [pairDesc], ?_⟩, ?_⟩, ?_⟩
  · rw [alternates_congr _ d₁.msgs (dirs_pairDesc hlen)]
    exact hd₁.alternates
  · simp [pairDesc, length_pairMsgs _ _ hlen, Desc.numMsgs]
  · refine blocksOkFrom_of _ 0 fun i g hg => ?_
    rw [zero_add]
    by_cases hi : i ≤ d₁.numMsgs
    · rw [blocks_pairDesc_getD hi, pairBlock, List.mem_append, List.mem_append] at hg
      rcases hg with (hg | hg) | hg
      · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
        exact okBool_relabel₁ hlen (by simpa using blocksOkFrom_getD _ 0 i hd₁.blocksOk g₀ hg₀)
      · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
        exact okBool_relabel₂ hlen hdir
          (by simpa using blocksOkFrom_getD _ 0 i hd₂.blocksOk g₀ hg₀)
      · split_ifs at hg with hm
        · have ho₁ := hd₁.out_lt
          have ho₂ := hd₂.out_lt
          have hpriv : ∀ v, v < 1 + d₁.priv + d₂.priv → (pairDesc d₁ d₂).held i v = true := by
            intro v hv
            simp [Desc.held, pairDesc, hv]
          refine okBool_toffoliGates (hpriv _ ?_) (hpriv _ ?_) (hpriv 0 (by omega)) ?_ ?_ ?_ g hg
          · rw [pos₁_priv ho₁]; omega
          · rw [pos₂_priv ho₂]; omega
          · rw [pos₁_priv ho₁, pos₂_priv ho₂]; omega
          · rw [pos₁_priv ho₁]; omega
          · rw [pos₂_priv ho₂]; omega
        · simp at hg
    · have : (pairDesc d₁ d₂).blocks.getD i [] = [] := by
        simp [pairDesc, List.getD_eq_getElem?_getD, show ¬ i < d₁.numMsgs + 1 by omega]
      rw [this] at hg
      simp at hg

end ShiQIP
