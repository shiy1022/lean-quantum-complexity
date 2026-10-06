/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.RejectFlag

/-!
# Q27 — the Bell-test description

`bellDesc d` runs `d` and then performs a Bell test. Write `W = d.totalWires`, `p = d.priv`,
`m = d.numMsgs`.

* **Wires.** The private register of `d` keeps its positions `0, …, p - 1`. Wire `p` is the
  Bell copy `B` and wire `p + 1` is the new output. The message registers of `d` move up by two
  (`bellShift`). After them come message `m` (verifier → prover, `W` wires, starting at
  `W + 2`) and message `m + 1` (prover → verifier, one wire `O' = 2W + 2`). In total there are
  `2W + 3` wires.
* **Blocks.** Blocks `j < m` are those of `d`, relabelled. Block `m` is block `m` of `d`, then
  `CNOT(out → B)`, then the swap of every wire of `d` still held during block `m` (private wires
  and messages to the verifier) into message `m`. Block `m + 1` is empty.
  Block `m + 2` is the Bell measurement on `(O', B)`, `CNOT(O' → B)` then `H(O')`, followed by
  "both read `0`" computed into the new output (`X`, `X`, Toffoli).

The honest prover receives everything the verifier holds except `B` (it keeps the messages it
was sent in memory, `QIP.Clean`) and returns the partner of `B` in the Bell state. This is possible exactly when `B` is maximally mixed, i.e. when `d` accepts with
probability `1/2`.
-/

namespace ShiQIP

/-- Relabel a wire of `d`: private wires stay, message wires move up by two. -/
def bellShift (d : Desc) (x : ℕ) : ℕ := if x < d.priv then x else x + 2

/-- The Bell copy wire. -/
def bellB (d : Desc) : ℕ := d.priv

/-- The new output wire. -/
def bellOut (d : Desc) : ℕ := d.priv + 1

/-- The first wire of message `m`. -/
def bellMsgOff (d : Desc) : ℕ := d.totalWires + 2

/-- The returned wire `O'` (message `m + 1`). -/
def bellO (d : Desc) : ℕ := 2 * d.totalWires + 2

/-- Swap every wire of `d` still held during block `m` into message `m`. -/
def swapAll (d : Desc) : List Gate :=
  (List.range d.totalWires).flatMap fun x =>
    if d.held d.numMsgs x then swapGates (bellShift d x) (bellMsgOff d + x) else []

/-- The Bell measurement and the "both zero" output. -/
def bellFinal (d : Desc) : List Gate :=
  [.cnot (bellO d) (bellB d), .h (bellO d), .x (bellO d), .x (bellB d)] ++
    toffoliGates (bellO d) (bellB d) (bellOut d)

/-- Block `j` of the Bell-test description. -/
def bellBlock (d : Desc) (j : ℕ) : List Gate :=
  if j < d.numMsgs then (d.blocks.getD j []).map (Gate.relabel (bellShift d))
  else if j = d.numMsgs then
    (d.blocks.getD j []).map (Gate.relabel (bellShift d)) ++
      [.cnot (bellShift d d.out) (bellB d)] ++ swapAll d
  else if j = d.numMsgs + 1 then []
  else bellFinal d

/-- **The Bell-test description.** -/
def bellDesc (d : Desc) : Desc where
  priv := d.priv + 2
  out := d.priv + 1
  msgs := d.msgs ++ [⟨.toProver, d.totalWires⟩, ⟨.toVerifier, 1⟩]
  blocks := (List.range (d.numMsgs + 3)).map (bellBlock d)

theorem numMsgs_bellDesc (d : Desc) : (bellDesc d).numMsgs = d.numMsgs + 2 := by
  simp [bellDesc, Desc.numMsgs]

theorem totalWires_bellDesc (d : Desc) : (bellDesc d).totalWires = 2 * d.totalWires + 3 := by
  simp only [Desc.totalWires, bellDesc, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem schedule_bellDesc (d : Desc) :
    (bellDesc d).msgs.map Message.dir = d.msgs.map Message.dir ++ [.toProver, .toVerifier] := by
  simp [bellDesc]

end ShiQIP
