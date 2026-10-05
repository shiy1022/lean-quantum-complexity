import «AMPUNI-replay-mark-restore-run»
import «AMPUNI-replay-reload-full-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayCycle

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The reload and mark-restore subroutines jointly reestablish the parser's
source and scratch conditions, while preserving the archived input for a
further copy. Their machine-level control labels are joined separately. -/
theorem reload_then_restore_state (count : Nat) (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S ShiTMReplayReload.source = [])
    (hscratch : S ShiTMReplayReload.scratch = [])
    (harchive : S ShiTMReplayReload.archive = s.reverse)
    (hmarks : S ShiTMReplayMarkRestore.marks =
      List.replicate count Cell.mark) :
    ∃ (T U : ∀ k, List (TopGam k)),
      ShiTMReplayReload.run^[2 * (s.length + 1)]
        (some ⟨some (0 : ShiTMReplayReload.ReloadLabel), v, S⟩) =
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
          j ≠ ShiTMReplayReload.archive → U j = S j := by
  obtain ⟨T, hreload, hTsource, hTscratch, hTarchive, hTframe⟩ :=
    ShiTMReplayReload.reload_input_run s v S hsource hscratch harchive
  have hTmarks : T ShiTMReplayMarkRestore.marks =
      List.replicate count Cell.mark := by
    rw [hTframe _ (by decide) (by decide) (by decide)]
    exact hmarks
  obtain ⟨U, hrestore, hUmarks, hUarchive, hUframe⟩ :=
    ShiTMReplayMarkRestore.restore_all_run count none T hTmarks
  refine ⟨T, U, hreload, hrestore, ?_, ?_, hUmarks, ?_, ?_⟩
  · rw [hUframe _ (by decide) (by decide)]
    exact hTsource
  · rw [hUframe _ (by decide) (by decide)]
    exact hTscratch
  · rw [hUarchive, hTarchive]
  · intro j hsrc hscratch' hmarks' harch
    rw [hUframe j harch hmarks', hTframe j hsrc hscratch' harch]

end ShiTMReplayCycle
