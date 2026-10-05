/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Syntax

/-!
# Q13 — resource accounting, and example descriptions

Resource measures of a description, fixed before any transformation is defined:

* `gateCount` — primitive gates over all blocks;
* `totalWires` — verifier wires, `priv + communication`;
* `communication` — total width of all messages;
* `numMsgs` — directed messages (one transfer each);
* `serialSize` — the exact length of the Boolean encoding of Q14 (`QIP.Encoding` proves the
  equality), with `serialSize_le` bounding it polynomially in the other measures for valid
  descriptions.

The examples instantiate one-, two-, three- and five-message descriptions (with a zero-width
message) and check validity, invalidity of ownership violations, and schedules by `decide`.
-/

namespace ShiQIP

/-- The encoded length of a gate (unary tag, then unary wire indices). -/
def Gate.encLen : Gate → ℕ
  | .h i => i + 2
  | .s i => i + 3
  | .t i => i + 4
  | .x i => i + 5
  | .cnot i j => i + j + 7

namespace Desc

variable (d : Desc)

/-- The number of primitive gates. -/
def gateCount : ℕ := (d.blocks.map List.length).sum

/-- The total number of message qubits. -/
def communication : ℕ := (d.msgs.map Message.width).sum

/-- The exact length of the Q14 encoding. -/
def serialSize : ℕ :=
  (d.priv + 1) + (d.out + 1) +
    (d.msgs.length + 1 + (d.msgs.map fun m => m.width + 2).sum) +
    (d.blocks.length + 1 + (d.blocks.map fun b => b.length + 1 + (b.map Gate.encLen).sum).sum)

theorem totalWires_eq : d.totalWires = d.priv + d.communication := rfl

end Desc

/-! ## Held wires are in range -/

theorem msgHeld_lt {j w : ℕ} :
    ∀ (ms : List Message) (k off : ℕ), msgHeld j w ms k off = true →
      w < off + (ms.map Message.width).sum
  | [], _, _, h => by simp [msgHeld] at h
  | m :: ms, k, off, h => by
    simp only [msgHeld, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨_, hw⟩, _⟩ | h
    · simp only [List.map_cons, List.sum_cons]; omega
    · have := msgHeld_lt ms (k + 1) (off + m.width) h
      simp only [List.map_cons, List.sum_cons]; omega

theorem Desc.held_lt {d : Desc} {j w : ℕ} (h : d.held j w = true) : w < d.totalWires := by
  unfold held at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  unfold totalWires
  rcases h with h | h
  · omega
  · exact msgHeld_lt _ _ _ h

theorem Gate.encLen_le {ok : ℕ → Bool} {W : ℕ} (hok : ∀ w, ok w = true → w < W) {g : Gate}
    (hg : g.okBool ok = true) : g.encLen ≤ 2 * W + 7 := by
  cases g <;> simp only [Gate.okBool, Bool.and_eq_true, bne_iff_ne] at hg <;>
    simp only [Gate.encLen]
  · have := hok _ hg; omega
  · have := hok _ hg; omega
  · have := hok _ hg; omega
  · have := hok _ hg; omega
  · have := hok _ hg.1.1; have := hok _ hg.1.2; omega

theorem Desc.blocksOkFrom_encLen {d : Desc} :
    ∀ (bs : List (List Gate)) (j : ℕ), d.blocksOkFrom bs j = true →
      ∀ b ∈ bs, ∀ g ∈ b, g.encLen ≤ 2 * d.totalWires + 7
  | [], _, _ => by simp
  | b :: bs, j, h => by
    simp only [blocksOkFrom, Bool.and_eq_true, List.all_eq_true] at h
    intro b' hb' g hg
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact Gate.encLen_le (fun w hw => Desc.held_lt hw) (h.1 g hg)
    · exact blocksOkFrom_encLen bs (j + 1) h.2 b' hb' g hg

/-! ## Components of validity -/

theorem Desc.Valid.out_lt {d : Desc} (h : d.Valid) : d.out < d.priv := by
  unfold Valid check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem Desc.Valid.alternates {d : Desc} (h : d.Valid) : Desc.alternates d.msgs = true := by
  unfold Valid check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem Desc.Valid.blocks_length {d : Desc} (h : d.Valid) :
    d.blocks.length = d.numMsgs + 1 := by
  unfold Valid check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem Desc.Valid.blocksOk {d : Desc} (h : d.Valid) : d.blocksOkFrom d.blocks 0 = true := by
  unfold Valid check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ## The polynomial size bound -/

theorem sum_map_width_add_two (ms : List Message) :
    (ms.map fun m => m.width + 2).sum = (ms.map Message.width).sum + 2 * ms.length := by
  induction ms with
  | nil => simp
  | cons m ms ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem sum_blocks_le {c : ℕ} :
    ∀ bs : List (List Gate), (∀ b ∈ bs, ∀ g ∈ b, g.encLen ≤ c) →
      (bs.map fun b => b.length + 1 + (b.map Gate.encLen).sum).sum ≤
        (c + 1) * (bs.map List.length).sum + bs.length
  | [], _ => by simp
  | b :: bs, h => by
    have hb : (b.map Gate.encLen).sum ≤ b.length * c := by
      have := List.sum_le_card_nsmul (b.map Gate.encLen) c
        (by intro x hx; obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx; exact h b (by simp) g hg)
      simpa using this
    have ih := sum_blocks_le bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- **Polynomial encoded size.** A valid description's encoding has length at most
`(gateCount + numMsgs + 3) * (2 * totalWires + 8)`. -/
theorem Desc.serialSize_le {d : Desc} (h : d.Valid) :
    d.serialSize ≤ (d.gateCount + d.numMsgs + 3) * (2 * d.totalWires + 8) := by
  have hout := h.out_lt
  have hB := h.blocks_length
  have hblocks := sum_blocks_le (c := 2 * d.totalWires + 7) d.blocks
    (Desc.blocksOkFrom_encLen d.blocks 0 h.blocksOk)
  unfold serialSize
  rw [sum_map_width_add_two]
  unfold gateCount numMsgs at *
  unfold totalWires at *
  rw [hB] at hblocks ⊢
  set G := (d.blocks.map List.length).sum
  set C := (d.msgs.map Message.width).sum
  set m := d.msgs.length
  nlinarith

/-! ## Examples -/

namespace Examples

/-- One message (prover → verifier), QMA-like: a two-qubit witness is received in block 1. -/
def oneMsg : Desc where
  priv := 2
  out := 0
  msgs := [⟨.toVerifier, 2⟩]
  blocks := [[], [.cnot 2 0, .h 3]]

/-- Two messages: the verifier sends one qubit, then receives one. -/
def twoMsg : Desc where
  priv := 1
  out := 0
  msgs := [⟨.toProver, 1⟩, ⟨.toVerifier, 1⟩]
  blocks := [[.h 1], [], [.cnot 2 0]]

/-- Three messages, the middle one of width zero. -/
def threeMsg : Desc where
  priv := 1
  out := 0
  msgs := [⟨.toVerifier, 1⟩, ⟨.toProver, 0⟩, ⟨.toVerifier, 1⟩]
  blocks := [[], [.cnot 1 0], [.x 0], [.cnot 2 0]]

/-- Five messages of width one. -/
def fiveMsg : Desc where
  priv := 1
  out := 0
  msgs := [⟨.toVerifier, 1⟩, ⟨.toProver, 1⟩, ⟨.toVerifier, 1⟩, ⟨.toProver, 1⟩,
    ⟨.toVerifier, 1⟩]
  blocks := [[], [.cnot 1 2], [], [.cnot 3 4], [], [.cnot 5 0]]

example : oneMsg.Valid ∧ oneMsg.HasSchedule 1 := by decide
example : twoMsg.Valid ∧ twoMsg.HasSchedule 2 := by decide
example : threeMsg.Valid ∧ threeMsg.HasSchedule 3 := by decide
example : fiveMsg.Valid ∧ fiveMsg.HasSchedule 5 := by decide

example : threeMsg.numMsgs = 3 ∧ threeMsg.totalWires = 3 ∧ threeMsg.communication = 2 ∧
    threeMsg.gateCount = 3 := by decide

/-- Touching a register after sending it is rejected. -/
example : ¬ ({ twoMsg with blocks := [[.h 1], [.x 1], [.cnot 2 0]] } : Desc).Valid := by decide

/-- Touching a register before receiving it is rejected. -/
example : ¬ ({ threeMsg with blocks := [[.x 2], [], [], []] } : Desc).Valid := by decide

/-- A CNOT with equal control and target is rejected. -/
example : ¬ ({ oneMsg with blocks := [[], [.cnot 2 2]] } : Desc).Valid := by decide

/-- An output wire outside the private register is rejected, even if wires exist there. -/
example : ¬ ({ oneMsg with out := 2 } : Desc).Valid := by decide

/-- A private register of width zero has no output wire, so it is rejected. -/
example : ¬ ({ priv := 0, out := 0, msgs := [], blocks := [[]] } : Desc).Valid := by decide

/-- The minimal valid description: zero messages, one private wire, no gates. -/
example : ({ priv := 1, out := 0, msgs := [], blocks := [[]] } : Desc).Valid := by decide

/-- Non-alternating messages are rejected. -/
example : ¬ (Desc.mk 1 0 [⟨.toVerifier, 0⟩, ⟨.toVerifier, 0⟩] [[], [], []]).Valid := by
  decide

/-- A verifier-first three-message protocol does not have the standard schedule. -/
example : ¬ (Desc.mk 1 0 [⟨.toProver, 0⟩, ⟨.toVerifier, 0⟩, ⟨.toProver, 0⟩]
    [[], [], [], []]).HasSchedule 3 := by decide

end Examples

end ShiQIP
