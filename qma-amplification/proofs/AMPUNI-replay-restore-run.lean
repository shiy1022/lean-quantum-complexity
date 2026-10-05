import «AMPUNI-replay-copy-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayPreface

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOutputEntry

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Restore every scratch cell to the input. At the end, insert the archive
sentinel and enter the already-proved delimiter-seeding machine. -/
theorem restore_all_run (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hscratch : S scratch = s) :
    ∃ U : ∀ k, List (TopGam k),
      run^[s.length + 1]
        (some { l := some restoreLabel, var := v, stk := S }) =
          some { l := some (oldLabel startLabel), var := none, stk := U }
      ∧ U scratch = []
      ∧ U source = s.reverse ++ S source
      ∧ U archive = Cell.mirrorEnd :: S archive
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
          (Cell.mirrorEnd :: S archive)) source = [] ++ S source
        rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]
        rfl
      · change (Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)) archive = Cell.mirrorEnd :: S archive
        rw [Function.update_self]
      · intro j hj0 hj1 hj2
        change (Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)) j = S j
        rw [Function.update_of_ne hj2, Function.update_of_ne hj1]
  | cons c tail ih =>
      let T : ∀ k : TopK, List (TopGam k) :=
        Function.update (Function.update S scratch tail) source (c :: S source)
      have hTscratch : T scratch = tail := by
        change (Function.update (Function.update S scratch tail) source
          (c :: S source)) scratch = tail
        rw [Function.update_of_ne (by decide), Function.update_self]
      have hTsource : T source = c :: S source := by
        change (Function.update (Function.update S scratch tail) source
          (c :: S source)) source = c :: S source
        rw [Function.update_self]
      have hTarchive : T archive = S archive := by
        change (Function.update (Function.update S scratch tail) source
          (c :: S source)) archive = S archive
        rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]
      have hTframe (j : TopK) (hj0 : j ≠ source) (hj1 : j ≠ scratch)
          (_hj2 : j ≠ archive) : T j = S j := by
        change (Function.update (Function.update S scratch tail) source
          (c :: S source)) j = S j
        rw [Function.update_of_ne hj0, Function.update_of_ne hj1]
      obtain ⟨U, hrun, hUscratch, hUsource, hUarchive, hUframe⟩ :=
        ih (some c) T hTscratch
      refine ⟨U, ?_, hUscratch, ?_, ?_, ?_⟩
      · have hfirst : run^[1]
            (some { l := some restoreLabel, var := v, stk := S }) =
              some { l := some restoreLabel, var := some c, stk := T } := by
          simpa [T] using restore_cell_step c tail v S hscratch
        have h := iterTwo run 1 (tail.length + 1) _ _ _ hfirst hrun
        have hcost : (c :: tail).length + 1 = 1 + (tail.length + 1) := by
          simp only [List.length_cons]
          omega
        rw [hcost]
        exact h
      · rw [hUsource, hTsource]
        simp [List.reverse_cons, List.append_assoc]
      · rw [hUarchive, hTarchive]
      · intro j hj0 hj1 hj2
        rw [hUframe j hj0 hj1 hj2, hTframe j hj0 hj1 hj2]

/-- The two traversals restore the original input and leave a delimited,
reversed archive on the retained output-index stack. -/
theorem archive_input_run (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S source = s) (hscratch : S scratch = [])
    (harchive : S archive = []) :
    ∃ U : ∀ k, List (TopGam k),
      run^[2 * (s.length + 1)]
        (some { l := some copyLabel, var := v, stk := S }) =
          some { l := some (oldLabel startLabel), var := none, stk := U }
      ∧ U source = s
      ∧ U scratch = []
      ∧ U archive = Cell.mirrorEnd :: s.reverse
      ∧ ∀ j : TopK, j ≠ source → j ≠ scratch → j ≠ archive → U j = S j := by
  obtain ⟨T, hcopy, hTsource, hTscratch, hTarchive, hTframe⟩ :=
    copy_all_run s v S hsource
  obtain ⟨U, hrestore, hUscratch, hUsource, hUarchive, hUframe⟩ :=
    restore_all_run s.reverse none T (by simpa [hscratch] using hTscratch)
  refine ⟨U, ?_, ?_, hUscratch, ?_, ?_⟩
  · have h := iterTwo run (s.length + 1) (s.reverse.length + 1)
      _ _ _ hcopy hrestore
    simpa [List.length_reverse, show 2 * (s.length + 1) =
      (s.length + 1) + (s.length + 1) by omega] using h
  · rw [hUsource, hTsource]
    simp
  · rw [hUarchive, hTarchive, harchive]
    simp
  · intro j hj0 hj1 hj2
    rw [hUframe j hj0 hj1 hj2, hTframe j hj0 hj1 hj2]

end ShiTMReplayPreface
