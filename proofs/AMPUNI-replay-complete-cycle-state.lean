import «AMPUNI-replay-cycle-state»
import «AMPUNI-replay-mark-split-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayCycle

open ShiTMLayoutMachine ShiTMRetainedTop

/-- One complete state-preserving replay cycle: separate the output-index
marks, reconstruct the source while retaining the archive, then return the
marks above its sentinel and empty parser scratch. The finite control graph
joining these three checked submachines is proved separately. -/
theorem complete_cycle_state (count : Nat) (s : List Cell)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = [])
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (harchive : V ShiTMReplayMarkSplit.archive =
      List.replicate count Cell.mark ++ Cell.mirrorEnd :: s.reverse) :
    ∃ (W T U : ∀ k, List (TopGam k)),
      ShiTMReplayMarkSplit.run^[count + 1]
        (some ⟨some false, none, V⟩) =
          some ⟨some true, some Cell.mirrorEnd, W⟩
      ∧ ShiTMReplayReload.run^[2 * (s.length + 1)]
          (some ⟨some (0 : ShiTMReplayReload.ReloadLabel),
            some Cell.mirrorEnd, W⟩) =
            some ⟨some (2 : ShiTMReplayReload.ReloadLabel), none, T⟩
      ∧ ShiTMReplayMarkRestore.run^[count + 1]
          (some ⟨some false, none, T⟩) =
            some ⟨some true, none, U⟩
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
  obtain ⟨W, hsplit, hWarchive, hWmarks, hWframe⟩ :=
    ShiTMReplayMarkSplit.split_all_run count s.reverse none V harchive
  have hWsource : W ShiTMReplayReload.source = [] := by
    rw [hWframe _ (by decide) (by decide)]
    exact hsource
  have hWscratch : W ShiTMReplayReload.scratch = [] := by
    rw [hWframe _ (by decide) (by decide)]
    exact hscratch
  have hWmarks' : W ShiTMReplayMarkRestore.marks =
      List.replicate count Cell.mark := by
    rw [hWmarks, hmarks]
    simp
  obtain ⟨T, U, hreload, hrestore, hUsource, hUscratch,
    hUmarks, hUarchive, hUframe⟩ :=
    reload_then_restore_state count s (some Cell.mirrorEnd) W
      hWsource hWscratch hWarchive hWmarks'
  exact ⟨W, T, U, hsplit, hreload, hrestore,
    hUsource, hUscratch, hUmarks, hUarchive,
    fun j hsrc hscratch' hmarks' harch =>
      (hUframe j hsrc hscratch' hmarks' harch).trans
        (hWframe j harch hmarks')⟩

end ShiTMReplayCycle
