/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiShallow_Core

/-!
# Q13 — syntax of quantum interactive verifiers

A verifier description `Desc` is finite first-order data: natural-number fields and lists. No field
is a function, so a description cannot hide an arbitrary computation.

## Wire layout

The verifier's wires are numbered `0, 1, …, totalWires - 1`:

* wires `0 … priv - 1` form the **private** register; the designated output wire `out` is one of
  them (`out < priv`), so a valid description always has an output qubit even when every message
  register has width zero;
* message `k` (0-indexed) owns a **fresh** block of `width k` consecutive wires starting at
  `msgOffset k = priv + width 0 + ⋯ + width (k - 1)`. A width may be zero.

## Messages and blocks

A message is one directed transfer, either prover → verifier (`Dir.toVerifier`) or verifier →
prover (`Dir.toProver`). A protocol with `m` messages has `m + 1` verifier circuit blocks: block
`j` runs before message `j`, and block `m` runs after the last message; then wire `out` is
measured, and outcome `1` means accept.

**Ownership.** During block `j` the verifier holds its private wires, every prover → verifier
message `k < j` (already received), and every verifier → prover message `k ≥ j` (not yet sent;
such a register starts in `|0⟩`). A valid block touches only held wires. In particular the
verifier never acts on a register after sending it, and never on a register before receiving it.

## Gates

Gates are the H/S/T/X/CNOT set of `ShiShallow.Instr`, written over natural-number wire indices.
`Gate.toInstr? n` converts a gate whose wires are in range (and, for CNOT, distinct) to the
established `ShiShallow.Instr n`, so no new gate meaning is introduced.

The three-message schedule is `stdSchedule 3 = [toVerifier, toProver, toVerifier]`:
prover → verifier, verifier → prover, prover → verifier.
-/

namespace ShiQIP

/-- The direction of one message. -/
inductive Dir where
  /-- prover → verifier -/
  | toVerifier
  /-- verifier → prover -/
  | toProver
  deriving DecidableEq, Repr

/-- One directed message: its direction and its width in qubits (possibly zero). -/
structure Message where
  dir : Dir
  width : ℕ
  deriving DecidableEq, Repr

/-- A gate of the H/S/T/X/CNOT set over natural-number wire indices. -/
inductive Gate where
  | h (i : ℕ)
  | s (i : ℕ)
  | t (i : ℕ)
  | x (i : ℕ)
  /-- control `i`, target `j` -/
  | cnot (i j : ℕ)
  deriving DecidableEq, Repr

/-- The wires a gate touches. -/
def Gate.wires : Gate → List ℕ
  | .h i | .s i | .t i | .x i => [i]
  | .cnot i j => [i, j]

/-- A gate is well formed over the wire predicate `ok` when it touches only `ok` wires and a
CNOT has distinct control and target. -/
def Gate.okBool (ok : ℕ → Bool) : Gate → Bool
  | .h i | .s i | .t i | .x i => ok i
  | .cnot i j => ok i && ok j && i != j

/-- The established gate meaning, for a gate whose wires are below `n` (and distinct, for CNOT). -/
def Gate.toInstr? (n : ℕ) : Gate → Option (ShiShallow.Instr n)
  | .h i => if hi : i < n then some (.h ⟨i, hi⟩) else none
  | .s i => if hi : i < n then some (.s ⟨i, hi⟩) else none
  | .t i => if hi : i < n then some (.t ⟨i, hi⟩) else none
  | .x i => if hi : i < n then some (.x ⟨i, hi⟩) else none
  | .cnot i j =>
    if h : i < n ∧ j < n ∧ i ≠ j then
      some (.cnot ⟨i, h.1⟩ ⟨j, h.2.1⟩ (fun e => h.2.2 (congrArg Fin.val e)))
    else none

theorem Gate.toInstr?_isSome_iff (n : ℕ) (g : Gate) :
    (g.toInstr? n).isSome ↔ g.okBool (fun w => decide (w < n)) = true := by
  cases g <;> simp only [toInstr?, okBool] <;> split_ifs <;> simp_all

/-- A verifier description. All fields are first-order data. -/
structure Desc where
  /-- width of the private register (it contains the output wire) -/
  priv : ℕ
  /-- the designated output wire; valid descriptions have `out < priv` -/
  out : ℕ
  /-- the messages, in order -/
  msgs : List Message
  /-- the verifier circuit blocks; block `j` runs before message `j` -/
  blocks : List (List Gate)
  deriving DecidableEq, Repr

namespace Desc

variable (d : Desc)

/-- The number of messages. -/
def numMsgs : ℕ := d.msgs.length

/-- The first wire of message register `k`. -/
def msgOffset (k : ℕ) : ℕ := d.priv + ((d.msgs.take k).map Message.width).sum

/-- The total number of wires. -/
def totalWires : ℕ := d.priv + (d.msgs.map Message.width).sum

end Desc

/-- Whether wire `w` lies in a message register held by the verifier during block `j`, scanning
the messages from index `k`, whose register starts at wire `off`. -/
def msgHeld (j w : ℕ) : List Message → ℕ → ℕ → Bool
  | [], _, _ => false
  | m :: ms, k, off =>
    (decide (off ≤ w ∧ w < off + m.width) &&
        (match m.dir with
          | .toVerifier => decide (k < j)
          | .toProver => decide (j ≤ k))) ||
      msgHeld j w ms (k + 1) (off + m.width)

namespace Desc

variable (d : Desc)

/-- Whether the verifier holds wire `w` during block `j`. -/
def held (j w : ℕ) : Bool := decide (w < d.priv) || msgHeld j w d.msgs 0 d.priv

/-- Consecutive messages alternate in direction. -/
def alternates : List Message → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a.dir != b.dir) && alternates (b :: rest)

/-- Every gate of every block touches only wires held during that block, starting at block
index `j`. -/
def blocksOkFrom : List (List Gate) → ℕ → Bool
  | [], _ => true
  | b :: bs, j => b.all (Gate.okBool (d.held j)) && blocksOkFrom bs (j + 1)

/-- The well-formedness checker. -/
def check : Bool :=
  decide (d.out < d.priv) && alternates d.msgs &&
    decide (d.blocks.length = d.msgs.length + 1) && d.blocksOkFrom d.blocks 0

/-- A valid verifier description. -/
def Valid : Prop := d.check = true

instance : DecidablePred Valid := fun d => inferInstanceAs (Decidable (d.check = true))

end Desc

/-! ## Message schedules -/

/-- The standard `k`-message schedule: directions alternate and the last message goes to the
verifier. `stdSchedule 3 = [toVerifier, toProver, toVerifier]`. -/
def stdSchedule (k : ℕ) : List Dir :=
  (List.range k).map fun i => if (k - 1 - i) % 2 = 0 then Dir.toVerifier else Dir.toProver

theorem stdSchedule_one : stdSchedule 1 = [.toVerifier] := rfl
theorem stdSchedule_two : stdSchedule 2 = [.toProver, .toVerifier] := rfl
theorem stdSchedule_three : stdSchedule 3 = [.toVerifier, .toProver, .toVerifier] := rfl
theorem stdSchedule_five :
    stdSchedule 5 = [.toVerifier, .toProver, .toVerifier, .toProver, .toVerifier] := rfl

/-- A description follows the standard `k`-message schedule: exactly `k` directed messages,
alternating, the last one to the verifier. -/
def Desc.HasSchedule (d : Desc) (k : ℕ) : Prop := d.msgs.map Message.dir = stdSchedule k

instance (d : Desc) (k : ℕ) : Decidable (d.HasSchedule k) :=
  inferInstanceAs (Decidable (_ = _))

theorem Desc.numMsgs_of_hasSchedule {d : Desc} {k : ℕ} (h : d.HasSchedule k) :
    d.numMsgs = k := by
  have := congrArg List.length h
  simpa [stdSchedule, numMsgs] using this

end ShiQIP
