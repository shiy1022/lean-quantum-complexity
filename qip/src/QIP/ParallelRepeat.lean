/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Pair.Valid

/-!
# Q25 — operational all-pass parallel repetition

`parRepeat d k` (`k ≥ 1`) runs `k` copies of a valid verifier description `d` in parallel.
Message `j` of the repetition batches the `k` copies of message `j`. The verifier accepts iff
all copies accept; the conjunction is computed by Toffoli gates into fresh ancillas. It is the
iterated paired description: `parRepeat d (k + 2) = pairDesc d (parRepeat d (k + 1))`.

* `parRepeat_valid`: it is a valid description with the same message schedule, in particular
  the same number of messages (`numMsgs_parRepeat`);
* **`value_parRepeat`**: `value (parRepeat d k) = value d ^ k` against **arbitrary** provers of
  the repeated protocol, whose strategies may be entangled across copies;
* resource counts: `totalWires_parRepeat` (`k·W + (k - 1)` wires), `communication_parRepeat`
  (`k` times the communication), `gateCount_parRepeat` (`k·G + 33 (k - 1)` gates).
-/

namespace ShiQIP

/-- `repeatAux d k` is `k + 1` copies of `d`. -/
def repeatAux (d : Desc) : ℕ → Desc
  | 0 => d
  | k + 1 => pairDesc d (repeatAux d k)

/-- **`k`-fold parallel repetition** (`k ≥ 1`; `parRepeat d 0 = d` by convention). -/
def parRepeat (d : Desc) (k : ℕ) : Desc := repeatAux d (k - 1)

theorem numMsgs_repeatAux (d : Desc) : ∀ k, (repeatAux d k).numMsgs = d.numMsgs
  | 0 => rfl
  | k + 1 => numMsgs_pairDesc (numMsgs_repeatAux d k).symm

theorem dirs_repeatAux (d : Desc) : ∀ k,
    (repeatAux d k).msgs.map Message.dir = d.msgs.map Message.dir
  | 0 => rfl
  | k + 1 => dirs_pairDesc (numMsgs_repeatAux d k).symm

theorem repeatAux_valid {d : Desc} (hd : d.Valid) : ∀ k, (repeatAux d k).Valid
  | 0 => hd
  | k + 1 => pairDesc_valid (numMsgs_repeatAux d k).symm (dirs_repeatAux d k).symm hd
      (repeatAux_valid hd k)

theorem value_repeatAux {d : Desc} (hd : d.Valid) : ∀ k, value (repeatAux d k) = value d ^ (k + 1)
  | 0 => by simp [repeatAux]
  | k + 1 => by
    rw [repeatAux, value_pairDesc (numMsgs_repeatAux d k).symm hd (repeatAux_valid hd k),
      value_repeatAux hd k]
    ring

theorem parRepeat_valid {d : Desc} (hd : d.Valid) (k : ℕ) : (parRepeat d k).Valid :=
  repeatAux_valid hd _

theorem numMsgs_parRepeat (d : Desc) (k : ℕ) : (parRepeat d k).numMsgs = d.numMsgs :=
  numMsgs_repeatAux d _

theorem schedule_parRepeat (d : Desc) (k : ℕ) :
    (parRepeat d k).msgs.map Message.dir = d.msgs.map Message.dir :=
  dirs_repeatAux d _

theorem hasSchedule_parRepeat {d : Desc} {m : ℕ} (h : d.HasSchedule m) (k : ℕ) :
    (parRepeat d k).HasSchedule m := by
  unfold Desc.HasSchedule at h ⊢
  rw [schedule_parRepeat, h]

/-- **Q25**: `value (parRepeat d k) = value d ^ k` for `k ≥ 1`, against arbitrary provers. -/
theorem value_parRepeat {d : Desc} (hd : d.Valid) {k : ℕ} (hk : 1 ≤ k) :
    value (parRepeat d k) = value d ^ k := by
  rw [parRepeat, value_repeatAux hd, Nat.sub_add_cancel hk]

/-! ## Resources -/

theorem totalWires_repeatAux (d : Desc) : ∀ k,
    (repeatAux d k).totalWires = (k + 1) * d.totalWires + k
  | 0 => by simp [repeatAux]
  | k + 1 => by
    rw [repeatAux, totalWires_pair_eq (numMsgs_repeatAux d k).symm, totalWires_repeatAux d k]
    ring

theorem totalWires_parRepeat (d : Desc) {k : ℕ} (hk : 1 ≤ k) :
    (parRepeat d k).totalWires = k * d.totalWires + (k - 1) := by
  rw [parRepeat, totalWires_repeatAux, Nat.sub_add_cancel hk]

theorem communication_pairDesc {d₁ d₂ : Desc} (hlen : d₁.numMsgs = d₂.numMsgs) :
    (pairDesc d₁ d₂).communication = d₁.communication + d₂.communication := by
  simp only [Desc.communication, pairDesc, pairMsgs_widths]
  exact sum_zw _ _ (by simpa [Desc.numMsgs] using hlen)

theorem communication_repeatAux (d : Desc) : ∀ k,
    (repeatAux d k).communication = (k + 1) * d.communication
  | 0 => by simp [repeatAux]
  | k + 1 => by
    rw [repeatAux, communication_pairDesc (numMsgs_repeatAux d k).symm, communication_repeatAux d k]
    ring

theorem communication_parRepeat (d : Desc) {k : ℕ} (hk : 1 ≤ k) :
    (parRepeat d k).communication = k * d.communication := by
  rw [parRepeat, communication_repeatAux, Nat.sub_add_cancel hk]

theorem sum_range_getD_length : ∀ (l : List (List Gate)),
    ((List.range l.length).map fun j => (l.getD j []).length).sum = (l.map List.length).sum
  | [] => rfl
  | b :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.map_cons, List.sum_cons]
    congr 1
    rw [← sum_range_getD_length l]
    congr 1

theorem gateCount_pairDesc {d₁ d₂ : Desc} (hlen : d₁.numMsgs = d₂.numMsgs) (hd₁ : d₁.Valid)
    (hd₂ : d₂.Valid) :
    (pairDesc d₁ d₂).gateCount = d₁.gateCount + d₂.gateCount + 33 := by
  have h₁ := hd₁.blocks_length
  have h₂ := hd₂.blocks_length
  simp only [Desc.gateCount, pairDesc, List.map_map]
  have e : ∀ j, (List.length ∘ pairBlock d₁ d₂) j =
      (d₁.blocks.getD j []).length + (d₂.blocks.getD j []).length +
        (if j = d₁.numMsgs then 33 else 0) := by
    intro j
    simp only [Function.comp_apply, pairBlock, List.length_append, List.length_map]
    split_ifs <;> simp [length_toffoliGates]
  rw [List.map_congr_left fun j _ => e j]
  rw [show (List.range (d₁.numMsgs + 1)).map (fun j => (d₁.blocks.getD j []).length +
      (d₂.blocks.getD j []).length + (if j = d₁.numMsgs then 33 else 0)) =
      List.zipWith (· + ·) (List.zipWith (· + ·)
        ((List.range (d₁.numMsgs + 1)).map fun j => (d₁.blocks.getD j []).length)
        ((List.range (d₁.numMsgs + 1)).map fun j => (d₂.blocks.getD j []).length))
        ((List.range (d₁.numMsgs + 1)).map fun j => if j = d₁.numMsgs then 33 else 0) by
    simp [List.zipWith_map, List.zipWith_self]]
  rw [sum_zw' _ _ (by simp), sum_zw' _ _ (by simp)]
  rw [← h₁, sum_range_getD_length, h₁, hlen, ← h₂, sum_range_getD_length]
  congr 1
  rw [h₂, ← hlen]
  simp [List.sum_map_ite, List.range_succ]
  intro a ha; omega
where
  sum_zw' (a b : List ℕ) (h : a.length = b.length) :
      (List.zipWith (· + ·) a b).sum = a.sum + b.sum := sum_zw a b h

theorem gateCount_repeatAux {d : Desc} (hd : d.Valid) : ∀ k,
    (repeatAux d k).gateCount = (k + 1) * d.gateCount + 33 * k
  | 0 => by simp [repeatAux]
  | k + 1 => by
    rw [repeatAux, gateCount_pairDesc (numMsgs_repeatAux d k).symm hd (repeatAux_valid hd k),
      gateCount_repeatAux hd k]
    ring

theorem gateCount_parRepeat {d : Desc} (hd : d.Valid) {k : ℕ} (hk : 1 ≤ k) :
    (parRepeat d k).gateCount = k * d.gateCount + 33 * (k - 1) := by
  rw [parRepeat, gateCount_repeatAux hd, Nat.sub_add_cancel hk]

end ShiQIP
