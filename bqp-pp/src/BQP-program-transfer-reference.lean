/-
BRIDGE-SIMk.  THE PER-GATE TRANSFER: the compiler's opcode blocks, read as operations on
BASIS STRINGS rather than on tapes.

BRIDGE-SIMb says what each emitted block does to a tape `l : List Bool`.  BRIDGE-SIMe says
what each gate does to a basis string `z : Bits m`, and supplies the dictionary
`l = List.ofFn z`.  Nothing yet says that these are the same thing, and until they do the
tape-side and basis-string-side halves of the semantic bridge do not meet.  This file is
that joint.

For each of the five constructors, and for the forward block `B` and the adjoint block
`BA` alike, running the block on the tape `List.ofFn z` with the head at wire 0 leaves the
head at wire 0, leaves both reject flags alone, adds the gate's phase increment, and
rewrites the tape to `List.ofFn` of the gate's forward action.  The control latch is left
in an unspecified state and is existentially quantified -- every block that reads it
writes it first.  Only the Hadamard block consumes a witness bit, and only it can raise
the underflow flag.  The output-wire test block is included, since the route-(A) program
needs it between the two passes.

The CNOT clause splits on the orientation of control and target, matching the two block
shapes the compiler emits; both land on the same basis-string action.  This is where the
tape-level CNOT theorem and the `Instr`-level one are finally identified.

Each of these statements has exactly the shape the alphabet-generic gate-list simulation
induction consumes, so instantiating that induction twice -- once at `(B, ph)` and once at
`(BA, padj)` -- turns them into the forward and adjoint sweeps of the whole program.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

theorem basisBlockTransfer :
    ∀ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (B BA : ∀ m : ℕ, Instr m → List ℕ)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (ph padj : ∀ m : ℕ, Instr m → Bool → Bits m → ZMod 8),
      -- BRIDGE-SIMb: the blocks, as tape operations with the head parked at wire 0
      (∀ (i : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([3] ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p + (if (l.drop i).headI then 1 else 0), [], l, ct, de, bd, w)) →
      (∀ (i : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([3, 3, 3, 3, 3, 3, 3] ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p + (if (l.drop i).headI then 7 else 0), [], l, ct, de, bd, w)) →
      (∀ (i : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([4] ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p + (if (l.drop i).headI then 2 else 0), [], l, ct, de, bd, w)) →
      (∀ (i : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([4, 4, 4] ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p + (if (l.drop i).headI then 6 else 0), [], l, ct, de, bd, w)) →
      (∀ (i : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([5] ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p, [], l.set i (!(l.drop i).headI), ct, de, bd, w)) →
      (∀ (i : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([2] ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p + (if (l.drop i).headI && w.headI then 4 else 0), [],
                l.set i w.headI, ct, de, bd || w.isEmpty, w.tail)) →
      (∀ (i : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([8] ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p, [], l, ct, de || !(l.drop i).headI, bd, w)) →
      (∀ (i j : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < j → j < l.length →
          (List.replicate i 1 ++ (([6] ++ (List.replicate (j - i) 1
              ++ ([7] ++ List.replicate (j - i) 0))) ++ List.replicate i 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p, [], l.set j (xor (l.drop j).headI (l.drop i).headI),
                (l.drop i).headI, de, bd, w)) →
      (∀ (i j : ℕ) (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          j < i → i < l.length →
          (List.replicate j 1 ++ ((List.replicate (i - j) 1 ++ ([6]
              ++ (List.replicate (i - j) 0 ++ [7]))) ++ List.replicate j 0)).foldl sTr
              (p, [], l, ct, de, bd, w)
            = (p, [], l.set j (xor (l.drop j).headI (l.drop i).headI),
                (l.drop i).headI, de, bd, w)) →
      -- BRIDGE-C2c: the per-gate blocks the compiler emits
      (∀ (m : ℕ) (i : Fin m), B m (Instr.h i)
          = List.replicate (i : ℕ) 1 ++ ([2] ++ List.replicate (i : ℕ) 0)) →
      (∀ (m : ℕ) (i : Fin m), B m (Instr.s i)
          = List.replicate (i : ℕ) 1 ++ ([4] ++ List.replicate (i : ℕ) 0)) →
      (∀ (m : ℕ) (i : Fin m), B m (Instr.t i)
          = List.replicate (i : ℕ) 1 ++ ([3] ++ List.replicate (i : ℕ) 0)) →
      (∀ (m : ℕ) (i : Fin m), B m (Instr.x i)
          = List.replicate (i : ℕ) 1 ++ ([5] ++ List.replicate (i : ℕ) 0)) →
      (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j), (i : ℕ) < (j : ℕ) →
          B m (Instr.cnot i j hij)
            = List.replicate (i : ℕ) 1 ++ (([6] ++ (List.replicate ((j : ℕ) - (i : ℕ)) 1
                ++ ([7] ++ List.replicate ((j : ℕ) - (i : ℕ)) 0)))
              ++ List.replicate (i : ℕ) 0)) →
      (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j), (j : ℕ) < (i : ℕ) →
          B m (Instr.cnot i j hij)
            = List.replicate (j : ℕ) 1 ++ ((List.replicate ((i : ℕ) - (j : ℕ)) 1
                ++ ([6] ++ (List.replicate ((i : ℕ) - (j : ℕ)) 0 ++ [7])))
              ++ List.replicate (j : ℕ) 0)) →
      (∀ (m : ℕ) (i : Fin m), BA m (Instr.h i) = B m (Instr.h i)) →
      (∀ (m : ℕ) (i : Fin m), BA m (Instr.x i) = B m (Instr.x i)) →
      (∀ (m : ℕ) (i : Fin m), BA m (Instr.s i)
          = List.replicate (i : ℕ) 1 ++ ([4, 4, 4] ++ List.replicate (i : ℕ) 0)) →
      (∀ (m : ℕ) (i : Fin m), BA m (Instr.t i)
          = List.replicate (i : ℕ) 1
              ++ ([3, 3, 3, 3, 3, 3, 3] ++ List.replicate (i : ℕ) 0)) →
      (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j),
          BA m (Instr.cnot i j hij) = B m (Instr.cnot i j hij)) →
      -- BRIDGE-SIMe: the tape dictionary
      (∀ (m : ℕ) (z : Bits m), (List.ofFn z).length = m) →
      (∀ (m : ℕ) (z : Bits m) (i : Fin m), ((List.ofFn z).drop (i : ℕ)).headI = z i) →
      (∀ (m : ℕ) (z : Bits m) (i : Fin m) (b : Bool),
          (List.ofFn z).set (i : ℕ) b = List.ofFn (Function.update z i b)) →
      -- BRIDGE-SIMe: the basis-string action and the two phase increments
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fw m (Instr.h i) a z = Function.update z i a) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), fw m (Instr.s i) a z = z) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), fw m (Instr.t i) a z = z) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fw m (Instr.x i) a z = Function.update z i (!(z i))) →
      (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a : Bool) (z : Bits m),
          fw m (Instr.cnot i j hij) a z = Function.update z j (xor (z j) (z i))) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          ph m (Instr.h i) a z = (if z i && a then 4 else 0)) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          ph m (Instr.s i) a z = (if z i then 2 else 0)) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          ph m (Instr.t i) a z = (if z i then 1 else 0)) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), ph m (Instr.x i) a z = 0) →
      (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a : Bool) (z : Bits m),
          ph m (Instr.cnot i j hij) a z = 0) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          padj m (Instr.h i) a z = (if z i && a then 4 else 0)) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          padj m (Instr.s i) a z = (if z i then 6 else 0)) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          padj m (Instr.t i) a z = (if z i then 7 else 0)) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), padj m (Instr.x i) a z = 0) →
      (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a : Bool) (z : Bits m),
          padj m (Instr.cnot i j hij) a z = 0) →
      -- THE FORWARD BLOCKS, on basis strings
      (∀ (m : ℕ) (i : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          ∃ ct' : Bool, (B m (Instr.h i)).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
            = (p + ph m (Instr.h i) w.headI z, [],
                List.ofFn (fw m (Instr.h i) w.headI z), ct', de, bd || w.isEmpty,
                w.tail))
      ∧ (∀ (m : ℕ) (g : Instr m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), (∀ i, g ≠ Instr.h i) →
          ∃ ct' : Bool, (B m g).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
            = (p + ph m g false z, [], List.ofFn (fw m g false z), ct', de, bd, w))
      -- THE ADJOINT BLOCKS, on basis strings
      ∧ (∀ (m : ℕ) (i : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          ∃ ct' : Bool, (BA m (Instr.h i)).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
            = (p + padj m (Instr.h i) w.headI z, [],
                List.ofFn (fw m (Instr.h i) w.headI z), ct', de, bd || w.isEmpty,
                w.tail))
      ∧ (∀ (m : ℕ) (g : Instr m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), (∀ i, g ≠ Instr.h i) →
          ∃ ct' : Bool, (BA m g).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
            = (p + padj m g false z, [], List.ofFn (fw m g false z), ct', de, bd, w))
      -- THE OUTPUT-WIRE TEST BLOCK, on basis strings
      ∧ (∀ (m : ℕ) (out : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          (List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0)).foldl sTr
              (p, [], List.ofFn z, ct, de, bd, w)
            = (p, [], List.ofFn z, ct, de || !(z out), bd, w)) := by
  intro sTr B BA fw ph padj hT hTd hS hSd hX hH hE8 hCl hCg
    hBh hBs hBt hBx hBclt hBcgt hBAh hBAx hBAs hBAt hBAc
    hlen hcell hset hfwh hfws hfwt hfwx hfwc hphh hphs hpht hphx hphc
    hpah hpas hpat hpax hpac
  have hlt : ∀ (m : ℕ) (z : Bits m) (i : Fin m), (i : ℕ) < (List.ofFn z).length := by
    intro m z i
    rw [hlen]
    exact i.isLt
  -- the two CNOT orientations, at basis-string level
  have hcnot : ∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (z : Bits m) (p : ZMod 8)
      (ct de bd : Bool) (w : List Bool),
      ∃ ct' : Bool, (B m (Instr.cnot i j hij)).foldl sTr
          (p, [], List.ofFn z, ct, de, bd, w)
        = (p, [], List.ofFn (Function.update z j (xor (z j) (z i))), ct', de, bd, w) := by
    intro m i j hij z p ct de bd w
    refine ⟨z i, ?_⟩
    have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.ext hc)
    rcases lt_or_gt_of_ne hne with hlt1 | hgt1
    · rw [hBclt m i j hij hlt1,
        hCl (i : ℕ) (j : ℕ) (List.ofFn z) p ct de bd w hlt1 (hlt m z j),
        hcell m z j, hcell m z i, hset m z j]
    · rw [hBcgt m i j hij hgt1,
        hCg (i : ℕ) (j : ℕ) (List.ofFn z) p ct de bd w hgt1 (hlt m z i),
        hcell m z j, hcell m z i, hset m z j]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- the forward Hadamard block
  · intro m i z p ct de bd w
    refine ⟨ct, ?_⟩
    rw [hBh m i, hH (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i), hcell m z i,
      hset m z i, hphh m i w.headI z, hfwh m i w.headI z]
  -- the other forward blocks
  · intro m g z p ct de bd w hg
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i =>
      refine ⟨ct, ?_⟩
      rw [hBs m i, hS (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i), hcell m z i,
        hphs m i false z, hfws m i false z]
    | t i =>
      refine ⟨ct, ?_⟩
      rw [hBt m i, hT (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i), hcell m z i,
        hpht m i false z, hfwt m i false z]
    | x i =>
      refine ⟨ct, ?_⟩
      rw [hBx m i, hX (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i), hcell m z i,
        hset m z i, hphx m i false z, hfwx m i false z, add_zero]
    | cnot i j hij =>
      obtain ⟨ct', hc⟩ := hcnot m i j hij z p ct de bd w
      refine ⟨ct', ?_⟩
      rw [hc, hphc m i j hij false z, hfwc m i j hij false z, add_zero]
  -- the adjoint Hadamard block
  · intro m i z p ct de bd w
    refine ⟨ct, ?_⟩
    rw [hBAh m i, hBh m i, hH (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i),
      hcell m z i, hset m z i, hpah m i w.headI z, hfwh m i w.headI z]
  -- the other adjoint blocks
  · intro m g z p ct de bd w hg
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i =>
      refine ⟨ct, ?_⟩
      rw [hBAs m i, hSd (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i), hcell m z i,
        hpas m i false z, hfws m i false z]
    | t i =>
      refine ⟨ct, ?_⟩
      rw [hBAt m i, hTd (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i), hcell m z i,
        hpat m i false z, hfwt m i false z]
    | x i =>
      refine ⟨ct, ?_⟩
      rw [hBAx m i, hBx m i, hX (i : ℕ) (List.ofFn z) p ct de bd w (hlt m z i),
        hcell m z i, hset m z i, hpax m i false z, hfwx m i false z, add_zero]
    | cnot i j hij =>
      obtain ⟨ct', hc⟩ := hcnot m i j hij z p ct de bd w
      refine ⟨ct', ?_⟩
      rw [hBAc m i j hij, hc, hpac m i j hij false z, hfwc m i j hij false z, add_zero]
  -- the output-wire test block
  · intro m out z p ct de bd w
    rw [hE8 (out : ℕ) (List.ofFn z) p ct de bd w (hlt m z out), hcell m z out]

end BQPBridgeReference
