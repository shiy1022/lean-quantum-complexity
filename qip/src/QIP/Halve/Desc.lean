/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Circuit.Predicates
import QIP.Gen.Cut

/-!
# Q31 — the halving description

Let `d` have `m = 2n + 1` messages (`n` even, `n ≥ 2`), `W` wires, and cut after block `c = n + 1`.
`halveDesc d n` has `n + 1` messages.

* **Wires.** The private register is a working copy of all `W` wires of `d` (same positions),
  then the coin `W`, the output `W + 1`, a control ancilla `W + 2`, and one zero-test ancilla per
  wire held during block `0` of `d`. Message `0'` has `W` wires (the cut state). Message
  `k' ≥ 1` has the larger of the widths of messages `n + k` and `n + 1 - k` of `d`; message `1'`
  has one more wire in front, the public copy of the coin.
* **Blocks.** Block `1'` swaps message `0'` into the working copy, prepares the coin with `H`
  and copies it into message `1'`. Then every block runs, controlled on the coin being `0`, the
  forward step (swap the arriving message in, the next block of `d`, swap the next message out),
  and controlled on the coin being `1`, the backward step (an inverse block of `d` instead). The
  final block copies the output of `d` (coin `0`) or tests that the wires held during block `0`
  are back to `0` (coin `1`, `ztGates`).
-/


namespace ShiQIP

variable (d : Desc) (n : ℕ)

/-- The width of message `j` of `d`. -/
def wd (j : ℕ) : ℕ := d.msgWidth j

/-- The width of message `k'`, without the coin copy. -/
def hw (k : ℕ) : ℕ := if k = 0 then d.totalWires else max (wd d (n + k)) (wd d (n + 1 - k))

/-- The wires held during block `0`, in order. -/
def held0 : List ℕ := (List.range d.totalWires).filter (d.held 0)

/-- The coin. -/
def hCoin : ℕ := d.totalWires

/-- The new output. -/
def hOut : ℕ := d.totalWires + 1

/-- The control ancilla. -/
def hCa : ℕ := d.totalWires + 2

/-- The zero-test ancillas. -/
def hAnc : List ℕ := (List.range (held0 d).length).map (· + (d.totalWires + 3))

/-- The private width. -/
def hPriv : ℕ := d.totalWires + 3 + (held0 d).length

/-- The messages of the halved description. -/
def hMsgs : List Message :=
  (List.range (n + 1)).map fun k =>
    ⟨if k % 2 = 0 then .toVerifier else .toProver, hw d n k + if k = 1 then 1 else 0⟩

/-- The first wire of message `k'`. -/
def hOff (k : ℕ) : ℕ := hPriv d + ((List.range k).map fun i => hw d n i + if i = 1 then 1 else 0).sum

/-- The first payload wire of message `k'` (after the coin copy for `k = 1`). -/
def hPay (k : ℕ) : ℕ := hOff d n k + if k = 1 then 1 else 0

/-- Swap the first `w` payload wires of message `k'` with register `j` of the working copy. -/
def swapMsg (k j : ℕ) : List Gate :=
  (List.range (wd d j)).flatMap fun i => swapGates (hPay d n k + i) (d.msgOffset j + i)

/-- Controlled on the coin being `0`. -/
def onF (gs : List Gate) : List Gate := [.x (hCoin d)] ++ ctrlGates (hCoin d) (hCa d) gs ++ [.x (hCoin d)]

/-- Controlled on the coin being `1`. -/
def onB (gs : List Gate) : List Gate := ctrlGates (hCoin d) (hCa d) gs

/-- The forward step of block `k'` (`2 ≤ k ≤ n`). -/
def fwdStep (k : ℕ) : List Gate :=
  (if (k - 1) % 2 = 0 then swapMsg d n (k - 1) (n + k - 1) else []) ++ d.blocks.getD (n + k) [] ++
    (if k % 2 = 1 then swapMsg d n k (n + k) else [])

/-- The backward step of block `k'` (`2 ≤ k ≤ n`). -/
def bwdStep (k : ℕ) : List Gate :=
  (if (k - 1) % 2 = 0 then swapMsg d n (k - 1) (n + 2 - k) else []) ++
    adjointGates (d.blocks.getD (n + 2 - k) []) ++
    (if k % 2 = 1 then swapMsg d n k (n + 1 - k) else [])

/-- Block `k'` of the halved description. -/
def hBlock (k : ℕ) : List Gate :=
  if k = 0 then []
  else if k = 1 then
    ((List.range d.totalWires).flatMap fun x => swapGates (hOff d n 0 + x) x) ++
      [.h (hCoin d), .cnot (hCoin d) (hOff d n 1)] ++
      onF d (swapMsg d n 1 (n + 1)) ++
      onB d (adjointGates (d.blocks.getD (n + 1) []) ++ swapMsg d n 1 n)
  else if k ≤ n then onF d (fwdStep d n k) ++ onB d (bwdStep d n k)
  else
    onF d (swapMsg d n n (2 * n) ++ d.blocks.getD (2 * n + 1) [] ++ [.cnot d.out (hOut d)]) ++
      onB d (swapMsg d n n 1 ++ adjointGates (d.blocks.getD 1 []) ++ adjointGates (d.blocks.getD 0 [])) ++
      ztGates (hCoin d) (hOut d) (held0 d) (hAnc d)

/-- **The halved description.** -/
def halveDesc : Desc where
  priv := hPriv d
  out := hOut d
  msgs := hMsgs d n
  blocks := (List.range (n + 2)).map (hBlock d n)

theorem numMsgs_halveDesc : (halveDesc d n).numMsgs = n + 1 := by
  simp [halveDesc, Desc.numMsgs, hMsgs]

/-! ## Layout facts -/

theorem priv_halveDesc : (halveDesc d n).priv = hPriv d := rfl

theorem length_hMsgs : (hMsgs d n).length = n + 1 := by simp [hMsgs]

theorem width_hMsgs (k : ℕ) (hk : k ≤ n) :
    (halveDesc d n).msgWidth k = hw d n k + if k = 1 then 1 else 0 := by
  simp [Desc.msgWidth, halveDesc, hMsgs, List.getElem?_map, List.getElem?_range (by omega : k < n + 1)]

theorem msgOffset_halveDesc (k : ℕ) (hk : k ≤ n + 1) : (halveDesc d n).msgOffset k = hOff d n k := by
  simp only [Desc.msgOffset, halveDesc, hOff, hPriv, hMsgs]
  congr 1
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]
  simp [List.map_map, Function.comp_def]

theorem dir_halveDesc (k : ℕ) (hk : k ≤ n) :
    ((halveDesc d n).msgs.map Message.dir).getD k .toVerifier =
      if k % 2 = 0 then .toVerifier else .toProver := by
  simp [halveDesc, hMsgs, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega : k < n + 1)]

theorem totalWires_halveDesc : (halveDesc d n).totalWires = hOff d n (n + 1) := by
  rw [← msgOffset_halveDesc d n (n + 1) le_rfl]
  simp only [Desc.totalWires, Desc.msgOffset]
  rw [List.take_of_length_le (by simp [halveDesc, length_hMsgs])]

theorem hOff_succ (k : ℕ) : hOff d n (k + 1) = hOff d n k + (hw d n k + if k = 1 then 1 else 0) := by
  simp only [hOff, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

theorem hOff_mono {k k' : ℕ} (h : k ≤ k') : hOff d n k ≤ hOff d n k' := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => rw [hOff_succ]; omega

theorem hPriv_le_hOff (k : ℕ) : hPriv d ≤ hOff d n k := by unfold hOff; omega

end ShiQIP
