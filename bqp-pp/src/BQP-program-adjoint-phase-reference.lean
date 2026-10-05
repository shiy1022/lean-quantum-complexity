/-
BRIDGE-SIMo.  THE PHASE HALF OF THE ADJOINT-PASS REVERSAL.

BRIDGE-SIMn showed that the reverse pass of the doubled program, run from the forward
endpoint on the reversed destroyed-bit list, returns to the start state and destroys the
reversed forward witness.  What remains for `C d = N d` -- beyond Finset bookkeeping --
is that the reverse pass pays exactly the NEGATED phase, so that the doubled program's
total exponent is the phase DIFFERENCE of the two `U`-paths mod 8.

That is what this file proves.  The cancellation is per gate and comes in two flavours.
For a non-Hadamard gate it is the adjoint-block identity `T† = +7` against `T = +1`,
`S† = +6` against `S = +2`, `X` and CNOT at zero, evaluated at the state the reverse pass
actually visits, namely the forward image.  For a Hadamard it is subtler and worth stating
explicitly: the adjoint block is the SAME block, its increment is again four-times-the-
and-of-the-two-bits, and the two bits are the same pair in the opposite order -- so the
two increments are EQUAL, not opposite, and they cancel only because four plus four is
zero mod eight.

Supporting laws proved here: the adjoint phase fold is additive over concatenation of
gate lists and ignores witness bits past the ones it consumes, the same two facts the
tape-side reversal needed.

Everything is in `ZMod 8`, so the truncated-subtraction hazard of the natural-number
formulation never arises.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

theorem adjointPhase :
    ∀ (N : ∀ m : ℕ, List (Instr m) → ℕ)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (ph padj : ∀ m : ℕ, Instr m → Bool → Bits m → ZMod 8)
      (Fwd : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → Bits m)
      (Bk : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → List Bool)
      (Pf Pa : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → ZMod 8),
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- BRIDGE-SIMc: the Hadamard block and the two phase increments
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fw m (Instr.h i) a z = Function.update z i a) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          ph m (Instr.h i) a z = (if z i && a then 4 else 0)) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          padj m (Instr.h i) a z = (if z i && a then 4 else 0)) →
      -- BRIDGE-SIMc (D): for every other gate the two increments cancel mod 8
      (∀ (m : ℕ) (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
          ph m g a z + padj m g a (fw m g a z) = 0) →
      -- BRIDGE-SIMf: the forward state and the destroyed-bit list
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Fwd m [] z w = z) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Fwd m (Instr.h i :: gs) z w = Fwd m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) → Fwd m (g :: gs) z w = Fwd m gs (fw m g false z) w) →
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Bk m [] z w = []) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Bk m (Instr.h i :: gs) z w
            = z i :: Bk m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) → Bk m (g :: gs) z w = Bk m gs (fw m g false z) w) →
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (Bk m gs z w).length = N m gs) →
      -- the two phase folds
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pf m [] z w = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Pf m (Instr.h i :: gs) z w
            = ph m (Instr.h i) w.headI z + Pf m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) →
          Pf m (g :: gs) z w = ph m g false z + Pf m gs (fw m g false z) w) →
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pa m [] z w = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Pa m (Instr.h i :: gs) z w
            = padj m (Instr.h i) w.headI z
                + Pa m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) →
          Pa m (g :: gs) z w = padj m g false z + Pa m gs (fw m g false z) w) →
      -- BRIDGE-SIMn: the Hadamard count, the concatenation laws, the tape reversal
      (∀ (m : ℕ) (gs : List (Instr m)), N m gs.reverse = N m gs) →
      (∀ (m : ℕ) (as bs : List (Instr m)) (z : Bits m) (w : List Bool),
          Fwd m (as ++ bs) z w = Fwd m bs (Fwd m as z w) (w.drop (N m as))) →
      (∀ (m : ℕ) (as : List (Instr m)) (z : Bits m) (w u : List Bool),
          w.length = N m as →
          Fwd m as z (w ++ u) = Fwd m as z w ∧ Bk m as z (w ++ u) = Bk m as z w) →
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          w.length = N m gs →
          Fwd m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse = z
            ∧ Bk m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse = w.reverse) →
      -- the adjoint phase fold is additive over concatenation
      (∀ (m : ℕ) (as bs : List (Instr m)) (z : Bits m) (w : List Bool),
          Pa m (as ++ bs) z w
            = Pa m as z w + Pa m bs (Fwd m as z w) (w.drop (N m as)))
      -- and ignores witness bits past the ones it consumes
      ∧ (∀ (m : ℕ) (as : List (Instr m)) (z : Bits m) (w u : List Bool),
          w.length = N m as → Pa m as z (w ++ u) = Pa m as z w)
      -- THE PHASE REVERSAL: the adjoint pass pays exactly the negated phase
      ∧ (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          w.length = N m gs →
          Pa m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse + Pf m gs z w = 0) := by
  intro N fw ph padj Fwd Bk Pf Pa hN0 hNh hNg hfwh hphh hpah hcan hF0 hFh hFg
    hB0 hBh hBg hBlen hPf0 hPfh hPfg hPa0 hPah hPag hNrev hFadd hpre hrev
  have htd : ∀ (w : List Bool) (k : ℕ), w.tail.drop k = w.drop (k + 1) := by
    intro w k
    cases w with
    | nil => simp
    | cons a s => rfl
  -- additivity of the adjoint phase fold
  have hPaadd : ∀ (m : ℕ) (as bs : List (Instr m)) (z : Bits m) (w : List Bool),
      Pa m (as ++ bs) z w = Pa m as z w + Pa m bs (Fwd m as z w) (w.drop (N m as)) := by
    intro m as
    induction as with
    | nil => intro bs z w; rw [hPa0, hF0, hN0]; simp
    | cons g as ih =>
      intro bs z w
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [List.cons_append, hPag m g (as ++ bs) z w hg, ih bs (fw m g false z) w,
          hPag m g as z w hg, hFg m g as z w hg, hNg m g as hg, add_assoc]
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [List.cons_append, hPah m i (as ++ bs) z w,
          ih bs (fw m (Instr.h i) w.headI z) w.tail, hPah m i as z w, hFh m i as z w,
          hNh m i as, htd w (N m as), add_assoc]
  -- the adjoint fold ignores the tail of the witness
  have hPapre : ∀ (m : ℕ) (as : List (Instr m)) (z : Bits m) (w u : List Bool),
      w.length = N m as → Pa m as z (w ++ u) = Pa m as z w := by
    intro m as
    induction as with
    | nil => intro z w u _; rw [hPa0, hPa0]
    | cons g as ih =>
      intro z w u hw
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hNg m g as hg] at hw
        rw [hPag m g as z (w ++ u) hg, hPag m g as z w hg, ih (fw m g false z) w u hw]
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [hNh m i as] at hw
        cases w with
        | nil => simp at hw
        | cons a w' =>
          have hw' : w'.length = N m as := by simpa using hw
          have e1 : ((a :: w') ++ u).headI = a := rfl
          have e2 : ((a :: w') ++ u).tail = w' ++ u := rfl
          have e3 : (a :: w').headI = a := rfl
          have e4 : (a :: w').tail = w' := rfl
          rw [hPah m i as z ((a :: w') ++ u), hPah m i as z (a :: w'), e1, e2, e3, e4,
            ih (fw m (Instr.h i) a z) w' u hw']
  -- THE PHASE REVERSAL
  have hmain : ∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      w.length = N m gs →
      Pa m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse + Pf m gs z w = 0 := by
    intro m gs
    induction gs with
    | nil =>
      intro z w _
      rw [hPf0]
      simp [hPa0]
    | cons g gs ih =>
      intro z w hw
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hNg m g gs hg] at hw
        have ihv := ih (fw m g false z) w hw
        obtain ⟨r1, _⟩ := hrev m gs (fw m g false z) w hw
        have hlen : ((Bk m gs (fw m g false z) w).reverse).length = N m gs.reverse := by
          rw [List.length_reverse, hBlen, hNrev]
        have hd : ((Bk m gs (fw m g false z) w).reverse).drop (N m gs.reverse) = [] := by
          apply List.drop_eq_nil_of_le
          exact le_of_eq hlen
        have hcanv := hcan m g hg false z
        rw [List.reverse_cons, hFg m g gs z w hg, hBg m g gs z w hg,
          hPaadd m gs.reverse [g] _ _, hPfg m g gs z w hg, r1, hd,
          hPag m g [] (fw m g false z) [] hg, hPa0]
        linear_combination ihv + hcanv
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [hNh m i gs] at hw
        cases w with
        | nil => simp at hw
        | cons a w' =>
          have hw' : w'.length = N m gs := by simpa using hw
          have e3 : (a :: w').headI = a := rfl
          have e4 : (a :: w').tail = w' := rfl
          have ihv := ih (fw m (Instr.h i) a z) w' hw'
          obtain ⟨r1, _⟩ := hrev m gs (fw m (Instr.h i) a z) w' hw'
          have hlen : ((Bk m gs (fw m (Instr.h i) a z) w').reverse).length
              = N m gs.reverse := by
            rw [List.length_reverse, hBlen, hNrev]
          have hd2 : (((Bk m gs (fw m (Instr.h i) a z) w').reverse) ++ [z i]).drop
              (N m gs.reverse) = [z i] := by
            rw [← hlen]
            exact List.drop_left
          have hzi : (fw m (Instr.h i) a z) i = a := by
            rw [hfwh m i a z]; simp
          have hq := hpre m gs.reverse (Fwd m gs (fw m (Instr.h i) a z) w')
            ((Bk m gs (fw m (Instr.h i) a z) w').reverse) [z i] hlen
          have hqa := hPapre m gs.reverse (Fwd m gs (fw m (Instr.h i) a z) w')
            ((Bk m gs (fw m (Instr.h i) a z) w').reverse) [z i] hlen
          have hhd : ([z i] : List Bool).headI = z i := rfl
          have hcanv : padj m (Instr.h i) (z i) (fw m (Instr.h i) a z)
              + ph m (Instr.h i) a z = 0 := by
            rw [hpah m i (z i) (fw m (Instr.h i) a z), hphh m i a z, hzi]
            cases hb : z i
            · cases ha : a <;> decide
            · cases ha : a <;> decide
          rw [List.reverse_cons, hFh m i gs z (a :: w'), hBh m i gs z (a :: w'),
            e3, e4, List.reverse_cons, hPaadd m gs.reverse [Instr.h i] _ _,
            hPfh m i gs z (a :: w'), e3, e4, hqa, hq.1, r1, hd2,
            hPah m i [] (fw m (Instr.h i) a z) [z i], hhd, hPa0]
          linear_combination ihv + hcanv
  exact ⟨hPaadd, hPapre, hmain⟩

end BQPBridgeReference
