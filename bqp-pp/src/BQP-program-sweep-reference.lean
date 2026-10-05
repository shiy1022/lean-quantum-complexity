/-
BRIDGE-SIMm.  THE GATE SWEEP OF THE COMPILED PROGRAM.

BRIDGE-SIMk transferred each individual block from the tape to basis strings.  This file
runs the induction over the whole gate list, so that the concatenated blocks of `gs` --
which is literally what the route-(A) compiler emits for the `U` pass and, with the
adjoint blocks and the reversed list, for the `U†` pass -- become a single statement about
the forward state `Fwd` and the accumulated phase `Pp`.

It is stated once, parametrically in the block map `Blk` and the per-gate phase increment
`Phs`, so that the SAME theorem covers both passes: instantiate at the forward blocks with
the forward phase, and at the adjoint blocks with the adjoint phase.

The witness hypothesis is `N m gs ≤ w.length`: the sweep then consumes exactly `N m gs`
bits, leaves `w.drop (N m gs)`, and -- this is the part that matters for the acceptance
conjunct -- raises NEITHER reject flag.  So along the compiled program the only sources of
rejection are the output-wire test, the endpoint test, and a wrong-length witness.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

theorem gateSweep :
    ∀ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (N : ∀ m : ℕ, List (Instr m) → ℕ)
      (Blk : ∀ m : ℕ, Instr m → List ℕ)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (Phs : ∀ m : ℕ, Instr m → Bool → Bits m → ZMod 8)
      (Fwd : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → Bits m)
      (Pp : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → ZMod 8),
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- BRIDGE-SIMk: the per-gate transfer, in either pass
      (∀ (m : ℕ) (i : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          ∃ ct' : Bool, (Blk m (Instr.h i)).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
            = (p + Phs m (Instr.h i) w.headI z, [],
                List.ofFn (fw m (Instr.h i) w.headI z), ct', de, bd || w.isEmpty,
                w.tail)) →
      (∀ (m : ℕ) (g : Instr m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), (∀ i, g ≠ Instr.h i) →
          ∃ ct' : Bool, (Blk m g).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
            = (p + Phs m g false z, [], List.ofFn (fw m g false z), ct', de, bd, w)) →
      -- BRIDGE-SIMf: the forward state
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Fwd m [] z w = z) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Fwd m (Instr.h i :: gs) z w = Fwd m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) → Fwd m (g :: gs) z w = Fwd m gs (fw m g false z) w) →
      -- BRIDGE-SIMg: the accumulated phase, for whichever pass
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pp m [] z w = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Pp m (Instr.h i :: gs) z w
            = Phs m (Instr.h i) w.headI z
                + Pp m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) →
          Pp m (g :: gs) z w = Phs m g false z + Pp m gs (fw m g false z) w) →
      -- THE SWEEP
      ∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
        (w : List Bool),
        N m gs ≤ w.length →
        ∃ ct' : Bool,
          ((gs.map (Blk m)).flatten).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
            = (p + Pp m gs z w, [], List.ofFn (Fwd m gs z w), ct', de, bd,
                w.drop (N m gs)) := by
  intro sTr N Blk fw Phs Fwd Pp hN0 hNh hNg hkh hkg hF0 hFh hFg hP0 hPh hPg
  intro m gs
  induction gs with
  | nil =>
    intro z p ct de bd w _
    refine ⟨ct, ?_⟩
    rw [hP0, hF0, hN0]
    simp
  | cons g gs ih =>
    intro z p ct de bd w hle
    have hmap : ((g :: gs).map (Blk m)).flatten
        = Blk m g ++ (gs.map (Blk m)).flatten := by simp
    by_cases hg : ∀ i, g ≠ Instr.h i
    · rw [hNg m g gs hg] at hle
      obtain ⟨ct1, h1⟩ := hkg m g z p ct de bd w hg
      obtain ⟨ct2, h2⟩ := ih (fw m g false z) (p + Phs m g false z) ct1 de bd w hle
      refine ⟨ct2, ?_⟩
      rw [hmap, List.foldl_append, h1, h2, hFg m g gs z w hg, hPg m g gs z w hg,
        hNg m g gs hg, add_assoc]
    · push_neg at hg
      obtain ⟨i, hi⟩ := hg
      subst hi
      rw [hNh m i gs] at hle
      have hw1 : 1 ≤ w.length := by omega
      have hnb : w.isEmpty = false := by
        cases w with
        | nil => simp at hw1
        | cons a s => rfl
      have hle' : N m gs ≤ w.tail.length := by
        cases w with
        | nil => simp at hw1
        | cons a s =>
          have : (a :: s).tail = s := rfl
          rw [this]
          simpa using hle
      obtain ⟨ct1, h1⟩ := hkh m i z p ct de bd w
      obtain ⟨ct2, h2⟩ := ih (fw m (Instr.h i) w.headI z)
        (p + Phs m (Instr.h i) w.headI z) ct1 de bd w.tail hle'
      refine ⟨ct2, ?_⟩
      have hdrop : w.tail.drop (N m gs) = w.drop (N m gs + 1) := by
        cases w with
        | nil => simp
        | cons a s =>
          show s.drop (N m gs) = (a :: s).drop (N m gs + 1)
          rfl
      rw [hmap, List.foldl_append, h1, hnb, Bool.or_false, h2, hFh m i gs z w,
        hPh m i gs z w, hNh m i gs, hdrop, add_assoc]

end BQPBridgeReference
