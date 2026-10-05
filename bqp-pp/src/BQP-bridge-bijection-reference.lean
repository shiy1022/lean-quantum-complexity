/-
BRIDGE-SIMh.  THE (Y, B) BIJECTION -- conjuncts (3) and (4) of the semantic bridge.

The forward simulation of a gate list reads one witness bit at each Hadamard and writes
it into that wire; the backward path sum of PATH-1b walks from an output string `y` and
writes one branch bit at each Hadamard into the SAME wire.  Gotcha 264: these two bit
strings are DIFFERENT.  The forward bit is the Hadamard's OUTPUT-side wire value, the
backward bit is its INPUT-side value, so the reindexing between them is real content,
not a coercion.  Both are in forward gate order, so no list reversal is involved.

This file makes the reindexing explicit and proves it is a bijection.  `Fwd` is the
forward state after running the whole list on a witness; `Bk` is the list of INPUT-side
values the Hadamards destroyed, again in forward gate order; `Wit` is the inverse, reading
a witness off a backward path.  The four theorems are:

* every forward branch is a backward path landing on the start state,
  `P gs (Fwd gs z w) (Bk gs z w) = z`  -- bridge conjunct (3);
* `Wit` recovers the witness, `Wit gs (Fwd gs z w) (Bk gs z w) = w`, hence `w ↦ (Fwd, Bk)`
  is INJECTIVE -- the only information-destroying step is a Hadamard write, and the value
  destroyed is exactly the recorded input-side bit (gotcha 265);
* `Wit` is a section: on any backward path landing on `z`, `Fwd` and `Bk` return the path;
* consequently `P gs y bits = z` holds exactly when a UNIQUE witness realises `(y, bits)`
  -- bridge conjunct (4).

The forward one-gate action `fw` and the fact that PATH-1b's `perm` inverts it are taken
as hypotheses; both are supplied by BRIDGE-SIMc.  Nothing here needs the phase.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

private def hWire {m : ℕ} : Instr m → Option (Fin m)
  | Instr.h i => some i
  | Instr.s _ => none
  | Instr.t _ => none
  | Instr.x _ => none
  | Instr.cnot _ _ _ => none

private def fwdL {m : ℕ} (fwm : Instr m → Bool → Bits m → Bits m) :
    List (Instr m) → Bits m → List Bool → Bits m
  | [], z, _ => z
  | g :: gs, z, w =>
      match hWire g with
      | some _ => fwdL fwm gs (fwm g w.headI z) w.tail
      | none => fwdL fwm gs (fwm g false z) w

private def bkL {m : ℕ} (fwm : Instr m → Bool → Bits m → Bits m) :
    List (Instr m) → Bits m → List Bool → List Bool
  | [], _, _ => []
  | g :: gs, z, w =>
      match hWire g with
      | some i => z i :: bkL fwm gs (fwm g w.headI z) w.tail
      | none => bkL fwm gs (fwm g false z) w

private def witL {m : ℕ} (Pm : List (Instr m) → Bits m → List Bool → Bits m) :
    List (Instr m) → Bits m → List Bool → List Bool
  | [], _, _ => []
  | g :: gs, y, bits =>
      match hWire g with
      | some i => Pm gs y bits.tail i :: witL Pm gs y bits.tail
      | none => witL Pm gs y bits

theorem reindex :
    ∀ (N : ∀ m : ℕ, List (Instr m) → ℕ)
      (P : ∀ m : ℕ, (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → Bits m)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m),
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- PATH-1b: the backward path map
      (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (y : Bits m) (bits : List Bool),
          P m perm [] y bits = y) →
      (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m)
          (i : Fin m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          P m perm (Instr.h i :: gs) y bits
            = Function.update (P m perm gs y bits.tail) i (bits.headD false)) →
      (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m)
          (g : Instr m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          (∀ i, g ≠ Instr.h i) →
          P m perm (g :: gs) y bits = perm g (P m perm gs y bits)) →
      -- BRIDGE-SIMc: the Hadamard block writes the witness bit
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fw m (Instr.h i) a z = Function.update z i a) →
      -- BRIDGE-SIMc: PATH-1b's `perm` inverts the forward block of every other gate
      (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
              Instr.apply g ψ z = coef g z * ψ (perm g z)) →
          ∀ (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
            perm g (fw m g a z) = z) →
      ∃ (Fwd : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → Bits m)
        (Bk : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → List Bool)
        (Wit : ∀ m : ℕ, (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → List Bool),
        -- the forward state after the whole gate list
        (∀ (m : ℕ) (z : Bits m) (w : List Bool), Fwd m [] z w = z)
        ∧ (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            Fwd m (Instr.h i :: gs) z w
              = Fwd m gs (fw m (Instr.h i) w.headI z) w.tail)
        ∧ (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            (∀ i, g ≠ Instr.h i) →
            Fwd m (g :: gs) z w = Fwd m gs (fw m g false z) w)
        -- the INPUT-side values the Hadamards destroyed, in forward gate order
        ∧ (∀ (m : ℕ) (z : Bits m) (w : List Bool), Bk m [] z w = [])
        ∧ (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            Bk m (Instr.h i :: gs) z w
              = z i :: Bk m gs (fw m (Instr.h i) w.headI z) w.tail)
        ∧ (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            (∀ i, g ≠ Instr.h i) →
            Bk m (g :: gs) z w = Bk m gs (fw m g false z) w)
        -- the witness read off a backward path
        ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (y : Bits m) (bits : List Bool),
            Wit m perm [] y bits = [])
        ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (i : Fin m)
              (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
            Wit m perm (Instr.h i :: gs) y bits
              = P m perm gs y bits.tail i :: Wit m perm gs y bits.tail)
        ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (g : Instr m)
              (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
            (∀ i, g ≠ Instr.h i) →
            Wit m perm (g :: gs) y bits = Wit m perm gs y bits)
        -- both reindexings have exactly one entry per Hadamard
        ∧ (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            (Bk m gs z w).length = N m gs)
        ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (gs : List (Instr m))
              (y : Bits m) (bits : List Bool),
            (Wit m perm gs y bits).length = N m gs)
        -- (3) EVERY FORWARD BRANCH IS A BACKWARD PATH LANDING ON THE START STATE
        ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
                Instr.apply g ψ z = coef g z * ψ (perm g z)) →
            ∀ (gs : List (Instr m)) (z : Bits m) (w : List Bool),
              P m perm gs (Fwd m gs z w) (Bk m gs z w) = z)
        -- `Wit` recovers the witness
        ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
                Instr.apply g ψ z = coef g z * ψ (perm g z)) →
            ∀ (gs : List (Instr m)) (z : Bits m) (w : List Bool),
              w.length = N m gs →
              Wit m perm gs (Fwd m gs z w) (Bk m gs z w) = w)
        -- and is a section on every backward path landing on the start state
        ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
                Instr.apply g ψ z = coef g z * ψ (perm g z)) →
            ∀ (gs : List (Instr m)) (y z : Bits m) (bits : List Bool),
              bits.length = N m gs → P m perm gs y bits = z →
              Fwd m gs z (Wit m perm gs y bits) = y
                ∧ Bk m gs z (Wit m perm gs y bits) = bits)
        -- INJECTIVITY of the reindexing
        ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
                Instr.apply g ψ z = coef g z * ψ (perm g z)) →
            ∀ (gs : List (Instr m)) (z : Bits m) (w1 w2 : List Bool),
              w1.length = N m gs → w2.length = N m gs →
              Fwd m gs z w1 = Fwd m gs z w2 → Bk m gs z w1 = Bk m gs z w2 → w1 = w2)
        -- (4) AND THE CORRESPONDENCE IS A BIJECTION ONTO THE SURVIVING PATHS
        ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
                Instr.apply g ψ z = coef g z * ψ (perm g z)) →
            ∀ (gs : List (Instr m)) (y z : Bits m) (bits : List Bool),
              bits.length = N m gs →
              (P m perm gs y bits = z
                ↔ ∃! w : List Bool,
                    w.length = N m gs ∧ Fwd m gs z w = y ∧ Bk m gs z w = bits)) := by
  intro N P fw hN0 hNh hNg hP0 hPh hPg hfwh hinv
  -- the non-Hadamard constructors have no wire
  have hnone : ∀ (m : ℕ) (g : Instr m), (∀ i, g ≠ Instr.h i) → hWire g = none := by
    intro m g hg
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i => rfl
    | t i => rfl
    | x i => rfl
    | cnot i j hij => rfl
  -- the recursion clauses
  have hF0 : ∀ (m : ℕ) (z : Bits m) (w : List Bool), fwdL (fw m) [] z w = z := by
    intro m z w; first | rfl | simp [fwdL]
  have hFh : ∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      fwdL (fw m) (Instr.h i :: gs) z w
        = fwdL (fw m) gs (fw m (Instr.h i) w.headI z) w.tail := by
    intro m i gs z w; first | rfl | simp [fwdL, hWire]
  have hFg : ∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      (∀ i, g ≠ Instr.h i) →
      fwdL (fw m) (g :: gs) z w = fwdL (fw m) gs (fw m g false z) w := by
    intro m g gs z w hg
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i => first | rfl | simp [fwdL, hWire]
    | t i => first | rfl | simp [fwdL, hWire]
    | x i => first | rfl | simp [fwdL, hWire]
    | cnot i j hij => first | rfl | simp [fwdL, hWire]
  have hB0 : ∀ (m : ℕ) (z : Bits m) (w : List Bool), bkL (fw m) [] z w = [] := by
    intro m z w; first | rfl | simp [bkL]
  have hBh : ∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      bkL (fw m) (Instr.h i :: gs) z w
        = z i :: bkL (fw m) gs (fw m (Instr.h i) w.headI z) w.tail := by
    intro m i gs z w; first | rfl | simp [bkL, hWire]
  have hBg : ∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      (∀ i, g ≠ Instr.h i) →
      bkL (fw m) (g :: gs) z w = bkL (fw m) gs (fw m g false z) w := by
    intro m g gs z w hg
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i => first | rfl | simp [bkL, hWire]
    | t i => first | rfl | simp [bkL, hWire]
    | x i => first | rfl | simp [bkL, hWire]
    | cnot i j hij => first | rfl | simp [bkL, hWire]
  have hW0 : ∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (y : Bits m)
      (bits : List Bool), witL (P m perm) [] y bits = [] := by
    intro m perm y bits; first | rfl | simp [witL]
  have hWh : ∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (i : Fin m)
      (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
      witL (P m perm) (Instr.h i :: gs) y bits
        = P m perm gs y bits.tail i :: witL (P m perm) gs y bits.tail := by
    intro m perm i gs y bits; first | rfl | simp [witL, hWire]
  have hWg : ∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (g : Instr m)
      (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
      (∀ i, g ≠ Instr.h i) →
      witL (P m perm) (g :: gs) y bits = witL (P m perm) gs y bits := by
    intro m perm g gs y bits hg
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i => first | rfl | simp [witL, hWire]
    | t i => first | rfl | simp [witL, hWire]
    | x i => first | rfl | simp [witL, hWire]
    | cnot i j hij => first | rfl | simp [witL, hWire]
  -- lengths
  have hBlen : ∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      (bkL (fw m) gs z w).length = N m gs := by
    intro m gs
    induction gs with
    | nil => intro z w; rw [hB0, hN0]; rfl
    | cons g gs ih =>
      intro z w
      cases hg : g with
      | h i =>
        rw [hBh, hNh]
        simp [ih]
      | s i =>
        rw [hBg m (Instr.s i) gs z w (by intro i'; simp),
          hNg m (Instr.s i) gs (by intro i'; simp)]
        exact ih _ _
      | t i =>
        rw [hBg m (Instr.t i) gs z w (by intro i'; simp),
          hNg m (Instr.t i) gs (by intro i'; simp)]
        exact ih _ _
      | x i =>
        rw [hBg m (Instr.x i) gs z w (by intro i'; simp),
          hNg m (Instr.x i) gs (by intro i'; simp)]
        exact ih _ _
      | cnot i j hij =>
        rw [hBg m (Instr.cnot i j hij) gs z w (by intro i'; simp),
          hNg m (Instr.cnot i j hij) gs (by intro i'; simp)]
        exact ih _ _
  have hWlen : ∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (gs : List (Instr m))
      (y : Bits m) (bits : List Bool), (witL (P m perm) gs y bits).length = N m gs := by
    intro m perm gs
    induction gs with
    | nil => intro y bits; rw [hW0, hN0]; rfl
    | cons g gs ih =>
      intro y bits
      cases hg : g with
      | h i =>
        rw [hWh, hNh]
        simp [ih]
      | s i =>
        rw [hWg m perm (Instr.s i) gs y bits (by intro i'; simp),
          hNg m (Instr.s i) gs (by intro i'; simp)]
        exact ih _ _
      | t i =>
        rw [hWg m perm (Instr.t i) gs y bits (by intro i'; simp),
          hNg m (Instr.t i) gs (by intro i'; simp)]
        exact ih _ _
      | x i =>
        rw [hWg m perm (Instr.x i) gs y bits (by intro i'; simp),
          hNg m (Instr.x i) gs (by intro i'; simp)]
        exact ih _ _
      | cnot i j hij =>
        rw [hWg m perm (Instr.cnot i j hij) gs y bits (by intro i'; simp),
          hNg m (Instr.cnot i j hij) gs (by intro i'; simp)]
        exact ih _ _
  -- (3) every forward branch is a backward path landing on the start state
  have hpath : ∀ (m : ℕ) (coef : Instr m → Bits m → ℂ)
      (perm : Instr m → Bits m → Bits m),
      (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
          Instr.apply g ψ z = coef g z * ψ (perm g z)) →
      ∀ (gs : List (Instr m)) (z : Bits m) (w : List Bool),
        P m perm gs (fwdL (fw m) gs z w) (bkL (fw m) gs z w) = z := by
    intro m coef perm hdata gs
    induction gs with
    | nil => intro z w; rw [hF0, hB0, hP0]
    | cons g gs ih =>
      intro z w
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hFg m g gs z w hg, hBg m g gs z w hg, hPg m perm g gs _ _ hg, ih]
        exact hinv m coef perm hdata g hg false z
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [hFh, hBh, hPh]
        have hstep : (z i :: bkL (fw m) gs (fw m (Instr.h i) w.headI z) w.tail).tail
            = bkL (fw m) gs (fw m (Instr.h i) w.headI z) w.tail := rfl
        rw [hstep, ih]
        have hhd : (z i :: bkL (fw m) gs (fw m (Instr.h i) w.headI z) w.tail).headD false
            = z i := rfl
        rw [hhd, hfwh m i w.headI z]
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [Function.update_apply, hk]
  -- `Wit` recovers the witness
  have hrec : ∀ (m : ℕ) (coef : Instr m → Bits m → ℂ)
      (perm : Instr m → Bits m → Bits m),
      (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
          Instr.apply g ψ z = coef g z * ψ (perm g z)) →
      ∀ (gs : List (Instr m)) (z : Bits m) (w : List Bool),
        w.length = N m gs →
        witL (P m perm) gs (fwdL (fw m) gs z w) (bkL (fw m) gs z w) = w := by
    intro m coef perm hdata gs
    induction gs with
    | nil =>
      intro z w hw
      rw [hN0] at hw
      rw [hW0]
      exact (List.length_eq_zero_iff.1 hw).symm
    | cons g gs ih =>
      intro z w hw
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hFg m g gs z w hg, hBg m g gs z w hg, hWg m perm g gs _ _ hg]
        rw [hNg m g gs hg] at hw
        exact ih (fw m g false z) w hw
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [hNh] at hw
        cases w with
        | nil => simp at hw
        | cons a w' =>
          have hw' : w'.length = N m gs := by simpa using hw
          have hhd : (a :: w').headI = a := rfl
          have htl : (a :: w').tail = w' := rfl
          rw [hFh, hBh, hWh, hhd, htl]
          have hstep : (z i :: bkL (fw m) gs (fw m (Instr.h i) a z) w').tail
              = bkL (fw m) gs (fw m (Instr.h i) a z) w' := rfl
          rw [hstep, ih (fw m (Instr.h i) a z) w' hw',
            hpath m coef perm hdata gs (fw m (Instr.h i) a z) w', hfwh m i a z]
          simp
  -- `Wit` is a section
  have hsec : ∀ (m : ℕ) (coef : Instr m → Bits m → ℂ)
      (perm : Instr m → Bits m → Bits m),
      (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
          Instr.apply g ψ z = coef g z * ψ (perm g z)) →
      ∀ (gs : List (Instr m)) (y z : Bits m) (bits : List Bool),
        bits.length = N m gs → P m perm gs y bits = z →
        fwdL (fw m) gs z (witL (P m perm) gs y bits) = y
          ∧ bkL (fw m) gs z (witL (P m perm) gs y bits) = bits := by
    -- `fw` is a two-sided inverse of `perm` on a finite basis-string space
    have hrinv : ∀ (m : ℕ) (coef : Instr m → Bits m → ℂ)
        (perm : Instr m → Bits m → Bits m),
        (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
            Instr.apply g ψ z = coef g z * ψ (perm g z)) →
        ∀ (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
          fw m g a (perm g z) = z := by
      intro m coef perm hdata g hg a z
      have hli : Function.LeftInverse (perm g) (fw m g a) :=
        fun u => hinv m coef perm hdata g hg a u
      have hinj : Function.Injective (fw m g a) := hli.injective
      have hbij : Function.Bijective (fw m g a) := Finite.injective_iff_bijective.1 hinj
      obtain ⟨u, hu⟩ := hbij.2 z
      rw [← hu, hli u]
    intro m coef perm hdata gs
    induction gs with
    | nil =>
      intro y z bits hb hpz
      rw [hN0] at hb
      rw [hW0, hF0, hB0]
      rw [hP0] at hpz
      exact ⟨hpz.symm ▸ rfl, (List.length_eq_zero_iff.1 hb).symm⟩
    | cons g gs ih =>
      intro y z bits hb hpz
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hNg m g gs hg] at hb
        rw [hPg m perm g gs y bits hg] at hpz
        have hz : fw m g false z = P m perm gs y bits := by
          rw [← hpz]
          exact hrinv m coef perm hdata g hg false (P m perm gs y bits)
        obtain ⟨e1, e2⟩ := ih y (P m perm gs y bits) bits hb rfl
        rw [hWg m perm g gs y bits hg, hFg m g gs z _ hg, hBg m g gs z _ hg, hz]
        exact ⟨e1, e2⟩
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [hNh] at hb
        cases bits with
        | nil => simp at hb
        | cons b bits' =>
          have hb' : bits'.length = N m gs := by simpa using hb
          have htl : (b :: bits').tail = bits' := rfl
          have hhd : (b :: bits').headD false = b := rfl
          rw [hPh, htl, hhd] at hpz
          set zz := P m perm gs y bits' with hzz
          have hzi : z i = b := by rw [← hpz]; simp
          have hzu : Function.update z i (zz i) = zz := by
            rw [← hpz]
            funext k
            by_cases hk : k = i
            · subst hk; simp
            · simp [Function.update_apply, hk]
          obtain ⟨e1, e2⟩ := ih y zz bits' hb' rfl
          rw [hWh, htl]
          have hhd2 : (zz i :: witL (P m perm) gs y bits').headI = zz i := rfl
          have htl2 : (zz i :: witL (P m perm) gs y bits').tail
              = witL (P m perm) gs y bits' := rfl
          rw [hFh, hBh, hhd2, htl2, hfwh m i (zz i) z, hzu]
          exact ⟨e1, by rw [e2, hzi]⟩
  refine ⟨fun m => fwdL (fw m), fun m => bkL (fw m), fun m perm => witL (P m perm),
    hF0, hFh, hFg, hB0, hBh, hBg, hW0, hWh, hWg, hBlen, hWlen, hpath, hrec, hsec,
    ?_, ?_⟩
  -- injectivity
  · intro m coef perm hdata gs z w1 w2 h1 h2 hfe hbe
    have e1 := hrec m coef perm hdata gs z w1 h1
    have e2 := hrec m coef perm hdata gs z w2 h2
    have hfe' : fwdL (fw m) gs z w1 = fwdL (fw m) gs z w2 := hfe
    have hbe' : bkL (fw m) gs z w1 = bkL (fw m) gs z w2 := hbe
    rw [← e1, ← e2, hfe', hbe']
  -- the bijection
  · intro m coef perm hdata gs y z bits hb
    constructor
    · intro hpz
      obtain ⟨e1, e2⟩ := hsec m coef perm hdata gs y z bits hb hpz
      refine ⟨witL (P m perm) gs y bits, ⟨hWlen m perm gs y bits, e1, e2⟩, ?_⟩
      intro w hw
      obtain ⟨hl, hf, hbk⟩ := hw
      have hf' : fwdL (fw m) gs z w = y := hf
      have hbk' : bkL (fw m) gs z w = bits := hbk
      rw [← hrec m coef perm hdata gs z w hl, hf', hbk']
    · intro hex
      obtain ⟨w, ⟨hl, hf, hbk⟩, _⟩ := hex
      rw [← hf, ← hbk]
      exact hpath m coef perm hdata gs z w

end BQPBridgeReference
