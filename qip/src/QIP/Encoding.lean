/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Resources

/-!
# Q14 — the Boolean encoding of verifier descriptions

A self-delimiting encoding over `Bool`:

* a natural `k` is `true ^ k` then `false` (`encNat`, the convention of `ShiBQP.encNat`);
* a direction is one bit, `true` for prover → verifier;
* a message is its direction bit, then its width;
* a gate is a unary tag `0 … 4` (`h, s, t, x, cnot`, the tags of `ShiBQP.encInstr`), then its
  wire indices;
* a list is its length, then the concatenated codes of its items (`encList`). This is injective
  because every item code is itself self-delimiting — the decoder of `QIP.Decode` proves it, and
  no unproved injectivity of a bare length-prefix/flatten operation is used;
* a description is `priv`, `out`, the message list, then the list of blocks, each block a list
  of gates. Every register size and every message boundary is written separately.

`encode_length` shows the length is exactly `Desc.serialSize`, hence polynomially bounded for
valid descriptions (`encode_length_le`).
-/

namespace ShiQIP

/-- Binary strings, as in `PvsNP.Str`. -/
abbrev Str := List Bool

/-- A natural number in unary, terminated by `false`. -/
def encNat (k : ℕ) : Str := List.replicate k true ++ [false]

/-- A direction: `true` for prover → verifier, `false` for verifier → prover. -/
def encDir : Dir → Str
  | .toVerifier => [true]
  | .toProver => [false]

def encMsg (m : Message) : Str := encDir m.dir ++ encNat m.width

def encGate : Gate → Str
  | .h i => encNat 0 ++ encNat i
  | .s i => encNat 1 ++ encNat i
  | .t i => encNat 2 ++ encNat i
  | .x i => encNat 3 ++ encNat i
  | .cnot i j => encNat 4 ++ encNat i ++ encNat j

/-- A list: its length, then the item codes. -/
def encList {α : Type*} (f : α → Str) (l : List α) : Str := encNat l.length ++ (l.map f).flatten

def encBlock (b : List Gate) : Str := encList encGate b

/-- The encoding of a verifier description. -/
def encode (d : Desc) : Str :=
  encNat d.priv ++ encNat d.out ++ encList encMsg d.msgs ++ encList encBlock d.blocks

/-! ## Exact lengths -/

@[simp] theorem encNat_length (k : ℕ) : (encNat k).length = k + 1 := by simp [encNat]

theorem encMsg_length (m : Message) : (encMsg m).length = m.width + 2 := by
  cases m with
  | mk dir w => cases dir <;> simp [encMsg, encDir]

theorem encGate_length (g : Gate) : (encGate g).length = g.encLen := by
  cases g <;> simp [encGate, Gate.encLen] <;> omega

theorem encList_length {α : Type*} (f : α → Str) (l : List α) :
    (encList f l).length = l.length + 1 + (l.map fun a => (f a).length).sum := by
  simp [encList, List.length_flatten, Function.comp_def]

theorem encBlock_length (b : List Gate) :
    (encBlock b).length = b.length + 1 + (b.map Gate.encLen).sum := by
  simp only [encBlock, encList_length, encGate_length]

/-- The encoded length is exactly the resource measure `serialSize`. -/
theorem encode_length (d : Desc) : (encode d).length = d.serialSize := by
  simp only [encode, List.length_append, encNat_length, encList_length, encMsg_length,
    encBlock_length, Desc.serialSize]

/-- **Polynomial encoded length** for valid descriptions. -/
theorem encode_length_le {d : Desc} (h : d.Valid) :
    (encode d).length ≤ (d.gateCount + d.numMsgs + 3) * (2 * d.totalWires + 8) := by
  rw [encode_length]
  exact Desc.serialSize_le h

end ShiQIP
