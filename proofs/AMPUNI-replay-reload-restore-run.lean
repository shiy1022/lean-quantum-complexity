import «AMPUNI-replay-reload-transfer-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayReload

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Restore scratch to the archive and replace its sentinel, leaving the
source ready for the next mapped-circuit pass. -/
theorem restore_all_run (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hscratch : S scratch = s) :
    ∃ U : ∀ k, List (TopGam k),
      run^[s.length + 1]
        (some { l := some (1 : ReloadLabel), var := v, stk := S }) =
          some { l := some (2 : ReloadLabel), var := none, stk := U }
      ∧ U scratch = []
      ∧ U source = S source
      ∧ U archive = Cell.mirrorEnd :: (s.reverse ++ S archive)
      ∧ ∀ j : TopK, j ≠ source → j ≠ scratch → j ≠ archive → U j = S j := by
  induction s generalizing v S with
  | nil =>
      let U : ∀ k : TopK, List (TopGam k) :=
        Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)
      refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [U] using restore_empty_step v S hscratch
      · change (Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)) scratch = []
        rw [Function.update_of_ne (by decide), Function.update_self]
      · change (Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)) source = S source
        rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]
      · change (Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)) archive =
            Cell.mirrorEnd :: ([] ++ S archive)
        rw [Function.update_self]
        rfl
      · intro j _ hj1 hj2
        change (Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)) j = S j
        rw [Function.update_of_ne hj2, Function.update_of_ne hj1]
  | cons c tail ih =>
      let T : ∀ k : TopK, List (TopGam k) :=
        Function.update (Function.update S scratch tail) archive
          (c :: S archive)
      have hTscratch : T scratch = tail := by
        change (Function.update (Function.update S scratch tail) archive
          (c :: S archive)) scratch = tail
        rw [Function.update_of_ne (by decide), Function.update_self]
      have hTsource : T source = S source := by
        change (Function.update (Function.update S scratch tail) archive
          (c :: S archive)) source = S source
        rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]
      have hTarchive : T archive = c :: S archive := by
        change (Function.update (Function.update S scratch tail) archive
          (c :: S archive)) archive = c :: S archive
        rw [Function.update_self]
      have hTframe (j : TopK) (hj0 : j ≠ source) (hj1 : j ≠ scratch)
          (hj2 : j ≠ archive) : T j = S j := by
        change (Function.update (Function.update S scratch tail) archive
          (c :: S archive)) j = S j
        rw [Function.update_of_ne hj2, Function.update_of_ne hj1]
      obtain ⟨U, hrun, hUscratch, hUsource, hUarchive, hUframe⟩ :=
        ih (some c) T hTscratch
      refine ⟨U, ?_, hUscratch, ?_, ?_, ?_⟩
      · have hfirst : run^[1]
            (some { l := some (1 : ReloadLabel), var := v, stk := S }) =
              some { l := some (1 : ReloadLabel), var := some c, stk := T } := by
          simpa [T] using restore_cell_step c tail v S hscratch
        rw [show (c :: tail).length + 1 = 1 + (tail.length + 1) by
          simp only [List.length_cons]
          omega]
        exact iterTwo run 1 (tail.length + 1) _ _ _ hfirst hrun
      · rw [hUsource, hTsource]
      · rw [hUarchive, hTarchive]
        simp [List.reverse_cons, List.append_assoc]
      · intro j hj0 hj1 hj2
        rw [hUframe j hj0 hj1 hj2, hTframe j hj0 hj1 hj2]

end ShiTMReplayReload
