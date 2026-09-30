/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Wire embeddings for layered quantum circuits -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

/-!
# Relabelling circuit wires along an injection

Given an injection `e : Fin m → Fin n`, these definitions relabel a circuit on `m` wires into
one on `n` wires: `embedInstr` on single instructions, `embedLayer` on layers, `embedCirc` on
layered circuits.

Relabelling is a PREREQUISITE for placing two circuits side by side on disjoint wire sets, or
for running several copies of one circuit in parallel -- but it is not by itself sufficient and
this bundle does not do it. Nothing here composes two embedded circuits: there is no layer-wise
merge, no pair of injections, and no disjointness hypothesis anywhere.

## What this bundle does and does NOT provide

It is PURELY SYNTACTIC. The embedding rewrites wire labels; it says nothing about semantics.
In particular this bundle does NOT provide, and no theorem here proves:

* any relation between `runLayered (embedCirc e he c)` and `runLayered c`. Stating that needs a
  map extending an `m`-wire state to an `n`-wire state (a tensor-with-identity construction on
  the complement of the image of `e`), which is NOT defined here;
* consequently nothing about `acceptProb`, `outDist`, or the induced matrices;
* nothing about circuits on DISJOINT images commuting, which is the property parallel
  composition actually needs.

Those are the next layer and are deliberately separate: a lemma about `runLayered` would have
to be stated against a state-extension definition this bundle does not have.

## The injectivity proof is an explicit argument, not data

`embedInstr` takes the injectivity proof `he` as an explicit argument, because the `Instr.cnot`
constructor requires its two wires to be distinct and `e i ≠ e j` is only available from
injectivity. `Function.Injective e` is a `Prop`, so `he` is NOT data: proof irrelevance in Lean
is definitional, any two proofs of it are defeq, and the family of embeddings is indexed by `e`
alone with `he` a proof obligation. Only the `cnot` branch uses `he`; the other four ignore it.

## Facts inherited from the import, not established here

`Instr`, `Layered` and the namespace `ShiShallow` come from `Def_ShiShallow_Core`, and so does
`Function.Injective` (transitively from Mathlib -- this file has no direct Mathlib import, so
the revision line in the header describes the environment, not a dependency of this file). The
`embedInstr` match has no catch-all and therefore assumes that file's exact constructor list
`h, s, t, x, cnot` with `cnot : (i j : Fin m) → i ≠ j → Instr m`; a new constructor there would
break this file rather than silently mis-handle it.

DEFINITIONS ONLY: no theorem is written in this file.
-/

namespace ShiEmbed

open ShiShallow

/-- Relabel the wires of a single instruction along an injection `e`. The injectivity proof is
needed for the `cnot` case: the constructor demands distinct wires, and `e i ≠ e j` follows
from `i ≠ j` only because `e` is injective. -/
def embedInstr {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) :
    Instr m → Instr n
  | .h i => .h (e i)
  | .s i => .s (e i)
  | .t i => .t (e i)
  | .x i => .x (e i)
  | .cnot i j hij => .cnot (e i) (e j) (fun h => hij (he h))

/-- Relabel every instruction of a layer. Gate order is preserved because this is
`List.map`; no lemma to that effect is provided here. -/
def embedLayer {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (l : List (Instr m)) : List (Instr n) :=
  l.map (embedInstr e he)

/-- Relabel every instruction of every layer of a circuit. Layer order and layer count are
preserved because this is `List.map`; no lemma to that effect is provided here, so in
particular `depth (embedCirc e he c) = depth c` is TRUE BY CONSTRUCTION but unproved in this
bundle. -/
def embedCirc {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (c : Layered m) : Layered n :=
  c.map (embedLayer e he)

end ShiEmbed
