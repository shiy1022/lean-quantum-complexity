import «AMPUNI-replay-cycle-lift-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayCycle

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def cycleCost (count : Nat) (s : List Cell) : Nat :=
  ((((count + 1) + 1) + 2 * (s.length + 1)) + 1) + (count + 1)

/-- The three replay subroutines and the two handoff transitions execute as
one finite TM2 machine. The resulting source, scratch, marks, and archive are
exactly ready for another copy's table initialization and circuit pass. -/
theorem full_cycle_run (count : Nat) (s : List Cell)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = [])
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (harchive : V ShiTMReplayMarkSplit.archive =
      List.replicate count Cell.mark ++ Cell.mirrorEnd :: s.reverse) :
    ∃ U : ∀ k, List (TopGam k),
      run^[cycleCost count s]
        (some ⟨some (splitLabel false), none, V⟩) =
          some ⟨some (restoreLabel true), none, U⟩
      ∧ U ShiTMReplayReload.source = s
      ∧ U ShiTMReplayReload.scratch = []
      ∧ U ShiTMReplayMarkRestore.marks = []
      ∧ U ShiTMReplayReload.archive =
          List.replicate count Cell.mark ++ Cell.mirrorEnd :: s.reverse
      ∧ ∀ j : TopK,
          j ≠ ShiTMReplayReload.source →
          j ≠ ShiTMReplayReload.scratch →
          j ≠ ShiTMReplayMarkRestore.marks →
          j ≠ ShiTMReplayReload.archive → U j = V j := by
  obtain ⟨W, T, U, hsplit, hreload, hrestore,
    hUsource, hUscratch, hUmarks, hUarchive, hUframe⟩ :=
    complete_cycle_state count s V hsource hscratch hmarks harchive
  have hsplit' : run^[count + 1]
      (some ⟨some (splitLabel false), none, V⟩) =
        some ⟨some (splitLabel true), some Cell.mirrorEnd, W⟩ := by
    simpa [liftCfg, splitLabel] using
      split_run_lift (count + 1)
        (some ⟨some false, none, V⟩)
        ⟨some true, some Cell.mirrorEnd, W⟩ rfl hsplit
  have htoReload : run^[1]
      (some ⟨some (splitLabel true), some Cell.mirrorEnd, W⟩) =
        some ⟨some (reloadLabel 0), some Cell.mirrorEnd, W⟩ := by
    simpa using split_done_step (some Cell.mirrorEnd) W
  have hreload' : run^[2 * (s.length + 1)]
      (some ⟨some (reloadLabel 0), some Cell.mirrorEnd, W⟩) =
        some ⟨some (reloadLabel 2), none, T⟩ := by
    simpa [liftCfg, reloadLabel] using
      reload_run_lift (2 * (s.length + 1))
        (some ⟨some (0 : ShiTMReplayReload.ReloadLabel),
          some Cell.mirrorEnd, W⟩)
        ⟨some (2 : ShiTMReplayReload.ReloadLabel), none, T⟩ rfl hreload
  have htoRestore : run^[1]
      (some ⟨some (reloadLabel 2), none, T⟩) =
        some ⟨some (restoreLabel false), none, T⟩ := by
    simpa using reload_done_step none T
  have hrestore' : run^[count + 1]
      (some ⟨some (restoreLabel false), none, T⟩) =
        some ⟨some (restoreLabel true), none, U⟩ := by
    simpa [liftCfg, restoreLabel] using
      restore_run_lift (count + 1)
        (some ⟨some false, none, T⟩)
        ⟨some true, none, U⟩ rfl hrestore
  refine ⟨U, ?_, hUsource, hUscratch, hUmarks, hUarchive, hUframe⟩
  have h₁ := iterTwo run (count + 1) 1 _ _ _ hsplit' htoReload
  have h₂ := iterTwo run ((count + 1) + 1)
    (2 * (s.length + 1)) _ _ _ h₁ hreload'
  have h₃ := iterTwo run (((count + 1) + 1) +
    2 * (s.length + 1)) 1 _ _ _ h₂ htoRestore
  exact iterTwo run ((((count + 1) + 1) +
    2 * (s.length + 1)) + 1) (count + 1) _ _ _ h₃ hrestore'

end ShiTMReplayCycle
