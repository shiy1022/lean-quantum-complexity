import «AMPUNI-replay-reload-restore-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayReload

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- A replay restores the original source but keeps the archive for one more
copy, using two linear traversals. -/
theorem reload_input_run (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S source = []) (hscratch : S scratch = [])
    (harchive : S archive = s.reverse) :
    ∃ U : ∀ k, List (TopGam k),
      run^[2 * (s.length + 1)]
        (some { l := some (0 : ReloadLabel), var := v, stk := S }) =
          some { l := some (2 : ReloadLabel), var := none, stk := U }
      ∧ U source = s
      ∧ U scratch = []
      ∧ U archive = Cell.mirrorEnd :: s.reverse
      ∧ ∀ j : TopK, j ≠ source → j ≠ scratch → j ≠ archive → U j = S j := by
  obtain ⟨T, htransfer, hTarchive, hTsource, hTscratch, hTframe⟩ :=
    transfer_all_run s.reverse v S harchive
  obtain ⟨U, hrestore, hUscratch, hUsource, hUarchive, hUframe⟩ :=
    restore_all_run s none T (by simpa [hscratch] using hTscratch)
  refine ⟨U, ?_, ?_, hUscratch, ?_, ?_⟩
  · have h := iterTwo run (s.reverse.length + 1) (s.length + 1)
      _ _ _ htransfer hrestore
    simpa [List.length_reverse, show 2 * (s.length + 1) =
      (s.length + 1) + (s.length + 1) by omega] using h
  · rw [hUsource, hTsource, hsource]
    simp
  · rw [hUarchive, hTarchive]
    simp
  · intro j hj0 hj1 hj2
    rw [hUframe j hj0 hj1 hj2, hTframe j hj0 hj1 hj2]

end ShiTMReplayReload
