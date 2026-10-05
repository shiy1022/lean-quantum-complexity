/-
BRIDGE-SIMn.  THE ADJOINT-PASS REVERSAL BIJECTION -- the mathematical content of
`C d = N d`.

Route (A) compiles the DOUBLED program `U ; Π-test ; U† ; endpoint-test` and counts its
single paths.  What has to be shown is that those single paths are in bijection with
ORDERED PAIRS of `U`-paths that land on the same output string.  This file proves the
half that is not bookkeeping: the reverse pass.

The adjoint pass emits the gate blocks in REVERSED order (gotcha 269: there is no
opcode-level inverse; CNOT is inverted as a BLOCK, and the adjoint pass just re-emits it,
gotcha 274).  Since each adjoint block has the SAME tape action as its forward block --
`T` and `S` act trivially, `X` and CNOT are involutions, and the Hadamard block overwrites
its wire with a fresh witness bit either way -- the reverse pass is simply the forward run
of the REVERSED gate list.  So the whole question is whether running the reversed list
forward from `y` and demanding arrival at `z` is the same thing as running the list
forward from `z` and demanding arrival at `y`.

It is, and the pairing of witnesses is explicit: the reverse pass's witness is the
REVERSAL of the forward pass's destroyed-bit list `Bk`, and the reverse pass's own
destroyed-bit list is the reversal of the forward witness.  The map is therefore an
involution on runs, which is exactly what makes the doubled program count ordered pairs.

Supporting laws proved here and needed anywhere the compiler concatenates blocks: the
Hadamard count is additive and reversal-invariant, `Fwd` and `Bk` are Kleisli-additive
over list concatenation, and both ignore any witness bits past the ones they consume.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

theorem adjointReversal :
    ∀ (N : ∀ m : ℕ, List (Instr m) → ℕ)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (Fwd : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → Bits m)
      (Bk : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → List Bool),
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- BRIDGE-SIMc: the Hadamard block writes the witness bit
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fw m (Instr.h i) a z = Function.update z i a) →
      -- BRIDGE-SIMc (D): every other block is its own inverse
      (∀ (m : ℕ) (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
          fw m g a (fw m g a z) = z) →
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
      -- the Hadamard count is additive and reversal-invariant
      (∀ (m : ℕ) (as bs : List (Instr m)), N m (as ++ bs) = N m as + N m bs)
      ∧ (∀ (m : ℕ) (gs : List (Instr m)), N m gs.reverse = N m gs)
      -- the run is Kleisli-additive over concatenation of gate lists
      ∧ (∀ (m : ℕ) (as bs : List (Instr m)) (z : Bits m) (w : List Bool),
          Fwd m (as ++ bs) z w = Fwd m bs (Fwd m as z w) (w.drop (N m as)))
      ∧ (∀ (m : ℕ) (as bs : List (Instr m)) (z : Bits m) (w : List Bool),
          Bk m (as ++ bs) z w
            = Bk m as z w ++ Bk m bs (Fwd m as z w) (w.drop (N m as)))
      -- and ignores witness bits past the ones it consumes
      ∧ (∀ (m : ℕ) (as : List (Instr m)) (z : Bits m) (w u : List Bool),
          w.length = N m as →
          Fwd m as z (w ++ u) = Fwd m as z w ∧ Bk m as z (w ++ u) = Bk m as z w)
      -- THE REVERSAL BIJECTION: running the reversed gate list from the forward
      -- endpoint, on the reversed destroyed-bit list, returns to the start and
      -- destroys exactly the reversed forward witness
      ∧ (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          w.length = N m gs →
          Fwd m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse = z
            ∧ Bk m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse = w.reverse) := by
  intro N fw Fwd Bk hN0 hNh hNg hfwh hfwinv hF0 hFh hFg hB0 hBh hBg hBlen
  have htd : ∀ (w : List Bool) (k : ℕ), w.tail.drop k = w.drop (k + 1) := by
    intro w k
    cases w with
    | nil => simp
    | cons a s => rfl
  -- additivity of the Hadamard count
  have hNadd : ∀ (m : ℕ) (as bs : List (Instr m)),
      N m (as ++ bs) = N m as + N m bs := by
    intro m as bs
    induction as with
    | nil => rw [hN0]; simp
    | cons g as ih =>
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [List.cons_append, hNg m g (as ++ bs) hg, ih, hNg m g as hg]
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [List.cons_append, hNh m i (as ++ bs), ih, hNh m i as]
        omega
  have hNrev : ∀ (m : ℕ) (gs : List (Instr m)), N m gs.reverse = N m gs := by
    intro m gs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [List.reverse_cons, hNadd, ih, hNg m g gs hg, hNg m g [] hg, hN0]
        try omega
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [List.reverse_cons, hNadd, ih, hNh m i gs, hNh m i [], hN0]
        try omega
  -- concatenation laws
  have hFadd : ∀ (m : ℕ) (as bs : List (Instr m)) (z : Bits m) (w : List Bool),
      Fwd m (as ++ bs) z w = Fwd m bs (Fwd m as z w) (w.drop (N m as)) := by
    intro m as
    induction as with
    | nil => intro bs z w; rw [hF0, hN0]; simp
    | cons g as ih =>
      intro bs z w
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [List.cons_append, hFg m g (as ++ bs) z w hg, ih bs (fw m g false z) w,
          hFg m g as z w hg, hNg m g as hg]
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [List.cons_append, hFh m i (as ++ bs) z w,
          ih bs (fw m (Instr.h i) w.headI z) w.tail, hFh m i as z w, hNh m i as,
          htd w (N m as)]
  have hBadd : ∀ (m : ℕ) (as bs : List (Instr m)) (z : Bits m) (w : List Bool),
      Bk m (as ++ bs) z w = Bk m as z w ++ Bk m bs (Fwd m as z w) (w.drop (N m as)) := by
    intro m as
    induction as with
    | nil => intro bs z w; rw [hB0, hF0, hN0]; simp
    | cons g as ih =>
      intro bs z w
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [List.cons_append, hBg m g (as ++ bs) z w hg, ih bs (fw m g false z) w,
          hBg m g as z w hg, hFg m g as z w hg, hNg m g as hg]
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [List.cons_append, hBh m i (as ++ bs) z w,
          ih bs (fw m (Instr.h i) w.headI z) w.tail, hBh m i as z w, hFh m i as z w,
          hNh m i as, htd w (N m as)]
        simp
  -- the run ignores the tail of the witness
  have hpre : ∀ (m : ℕ) (as : List (Instr m)) (z : Bits m) (w u : List Bool),
      w.length = N m as →
      Fwd m as z (w ++ u) = Fwd m as z w ∧ Bk m as z (w ++ u) = Bk m as z w := by
    intro m as
    induction as with
    | nil => intro z w u _; rw [hF0, hF0, hB0, hB0]; exact ⟨rfl, rfl⟩
    | cons g as ih =>
      intro z w u hw
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hNg m g as hg] at hw
        rw [hFg m g as z (w ++ u) hg, hFg m g as z w hg, hBg m g as z (w ++ u) hg,
          hBg m g as z w hg]
        exact ih (fw m g false z) w u hw
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
          rw [hFh m i as z ((a :: w') ++ u), hFh m i as z (a :: w'),
            hBh m i as z ((a :: w') ++ u), hBh m i as z (a :: w'), e1, e2, e3, e4]
          obtain ⟨p1, p2⟩ := ih (fw m (Instr.h i) a z) w' u hw'
          exact ⟨p1, by rw [p2]⟩
  -- THE REVERSAL BIJECTION
  have hrev : ∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      w.length = N m gs →
      Fwd m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse = z
        ∧ Bk m gs.reverse (Fwd m gs z w) (Bk m gs z w).reverse = w.reverse := by
    intro m gs
    induction gs with
    | nil =>
      intro z w hw
      rw [hN0] at hw
      have hwn : w = [] := List.length_eq_zero_iff.1 hw
      subst hwn
      rw [hF0, hB0]
      simp [hF0, hB0]
    | cons g gs ih =>
      intro z w hw
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hNg m g gs hg] at hw
        obtain ⟨p1, p2⟩ := ih (fw m g false z) w hw
        have hlen : ((Bk m gs (fw m g false z) w).reverse).length = N m gs.reverse := by
          rw [List.length_reverse, hBlen, hNrev]
        have hd : ((Bk m gs (fw m g false z) w).reverse).drop (N m gs.reverse) = [] := by
          apply List.drop_eq_nil_of_le
          exact le_of_eq hlen
        rw [List.reverse_cons, hFg m g gs z w hg, hBg m g gs z w hg,
          hFadd m gs.reverse [g] _ _, hBadd m gs.reverse [g] _ _, p1, p2, hd]
        refine ⟨?_, ?_⟩
        · rw [hFg m g [] (fw m g false z) [] hg, hF0]
          exact hfwinv m g hg false z
        · rw [hBg m g [] (fw m g false z) [] hg, hB0]
          simp
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
          obtain ⟨p1, p2⟩ := ih (fw m (Instr.h i) a z) w' hw'
          have hlen : ((Bk m gs (fw m (Instr.h i) a z) w').reverse).length
              = N m gs.reverse := by
            rw [List.length_reverse, hBlen, hNrev]
          have hzi : (fw m (Instr.h i) a z) i = a := by
            rw [hfwh m i a z]; simp
          have hzz : fw m (Instr.h i) (z i) (fw m (Instr.h i) a z) = z := by
            rw [hfwh m i a z, hfwh m i (z i) (Function.update z i a)]
            funext k
            by_cases hk : k = i
            · subst hk; simp
            · simp [Function.update_apply, hk]
          rw [List.reverse_cons, hFh m i gs z (a :: w'), hBh m i gs z (a :: w'),
            e3, e4, List.reverse_cons, hFadd m gs.reverse [Instr.h i] _ _,
            hBadd m gs.reverse [Instr.h i] _ _]
          obtain ⟨q1, q2⟩ := hpre m gs.reverse (Fwd m gs (fw m (Instr.h i) a z) w')
            ((Bk m gs (fw m (Instr.h i) a z) w').reverse) [z i] hlen
          have hd2 : (((Bk m gs (fw m (Instr.h i) a z) w').reverse) ++ [z i]).drop
              (N m gs.reverse) = [z i] := by
            rw [← hlen]
            exact List.drop_left
          rw [q1, q2, p1, p2, hd2]
          refine ⟨?_, ?_⟩
          · rw [hFh m i [] (fw m (Instr.h i) a z) [z i], hF0]
            have : ([z i] : List Bool).headI = z i := rfl
            rw [this]
            exact hzz
          · rw [hBh m i [] (fw m (Instr.h i) a z) [z i], hB0, hzi]
            simp
  exact ⟨hNadd, hNrev, hFadd, hBadd, hpre, hrev⟩

end BQPBridgeReference
