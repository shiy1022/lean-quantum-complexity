import «AMPUNI-copy-stage-with-skip-mirror-run»
import «AMPUNI-piece-controller-program-tables»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Replay, copy-specific table construction, and mirror setup form one run
of the corrected finite machine up to the next circuit-parser entry. -/
theorem cycle_to_parser_run (copy : Fin 3)
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = [])
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (harchive : V ShiTMReplayMarkSplit.archive =
      List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse)
    (hret : Retained n (F.wit n) (F.anc n) V)
    (h10 : V (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (W U T P : ∀ k, List (TopGam k)),
      run^[cycleSkipCost F n + ShiTMReplayTableClear.clearCost W + 1 +
        (scheduleCost n (F.wit n) (F.anc n) (program copy) + 1 + 1) +
        ((2 * (T (.inl (.inl (1 : Fin 14)))).length + 3) +
          (2 * (T (.inl (.inl (2 : Fin 14)))).length + 3) + 1)]
        (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
          (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.parserLabel copy
          (.inl (.inr .circuitHeader)))), none, P⟩
      ∧ tableState T =
          runCommands n (F.wit n) (F.anc n) (program copy) (tableState U)
      ∧ tableState T =
          (pieceCells Prod.fst (expectedPieces copy n (F.wit n) (F.anc n)),
           pieceCells Prod.snd (expectedPieces copy n (F.wit n) (F.anc n)))
      ∧ P ShiTMReplayReload.source =
          (ShiBQP.encCirc (F.circ n)).map bit
      ∧ P ShiTMReplayReload.scratch = []
      ∧ P ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ P (.inl (.inl (1 : Fin 14))) = T (.inl (.inl (1 : Fin 14)))
      ∧ P (.inl (.inl (2 : Fin 14))) = T (.inl (.inl (2 : Fin 14)))
      ∧ P (.inl (.inl (8 : Fin 14))) =
          (T (.inl (.inl (1 : Fin 14)))).reverse ++ [Cell.mirrorEnd]
      ∧ P (.inl (.inl (9 : Fin 14))) =
          (T (.inl (.inl (2 : Fin 14)))).reverse ++ [Cell.mirrorEnd]
      ∧ P (.inl (.inl (10 : Fin 14))) = []
      ∧ Retained n (F.wit n) (F.anc n) P
      ∧ P ShiTMReplayMarkRestore.marks = []
      ∧ ∀ j, CopyStable j → OutsideWrites j →
          j ≠ .inl (.inl (10 : Fin 14)) → P j = V j := by
  obtain ⟨W, U, T, v', hchain, htable, hUwidth, hUbase, hretT, hTsource,
    hTscratch, hTarchive, hT8, hT9, hT10, hTmarks, hTstable⟩ :=
    cycle_skip_clear_program_run copy F n V
      hsource hscratch hmarks harchive hret h10
  obtain ⟨P, hmirror, hP1, hP2, hP8, hP9, hP10, hframe⟩ :=
    mirror_run_to_parser copy
      (T (.inl (.inl (1 : Fin 14))))
      (T (.inl (.inl (2 : Fin 14)))) v' T
      rfl rfl hT8 hT9 hT10
  have hUtable : tableState U = ([], []) := by
    change U (.inl (.inl (1 : Fin 14))) = [] at hUwidth
    change U (.inl (.inl (2 : Fin 14))) = [] at hUbase
    exact Prod.ext hUwidth hUbase
  have htableExact : tableState T =
      (pieceCells Prod.fst (expectedPieces copy n (F.wit n) (F.anc n)),
       pieceCells Prod.snd (expectedPieces copy n (F.wit n) (F.anc n))) := by
    rw [htable, hUtable]
    fin_cases copy
    · simpa [expectedPieces] using
        (ShiTMPieceSchedule.run_program0 n (F.wit n) (F.anc n) [] [])
    · simpa [expectedPieces] using
        (ShiTMPieceSchedule.run_program1 n (F.wit n) (F.anc n) [] [])
    · simpa [expectedPieces] using
        (ShiTMPieceSchedule.run_program2 n (F.wit n) (F.anc n) [] [])
  refine ⟨W, U, T, P, ?_, htable, htableExact, ?_, ?_, ?_,
    hP1, hP2, hP8, hP9, hP10, ?_, ?_, ?_⟩
  · exact iterTwo run
      (cycleSkipCost F n + ShiTMReplayTableClear.clearCost W + 1 +
        (scheduleCost n (F.wit n) (F.anc n) (program copy) + 1 + 1))
      ((2 * (T (.inl (.inl (1 : Fin 14)))).length + 3) +
        (2 * (T (.inl (.inl (2 : Fin 14)))).length + 3) + 1)
      _ _ _ hchain hmirror
  · exact (hframe _ (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hTsource
  · exact (hframe _ (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hTscratch
  · exact (hframe _ (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hTarchive
  · rcases hretT with ⟨h0, h1, h2⟩
    exact ⟨
      (hframe _ (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans h0,
      (hframe _ (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans h1,
      (hframe _ (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans h2⟩
  · exact (hframe _ (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hTmarks
  · intro j hstable houtside h10'
    rcases hstable with ⟨hsrc, hscratch', hmarks', harch,
      h1, h2, h8, h9⟩
    exact (hframe j h1 h2 h8 h9 h10').trans
      (hTstable j ⟨hsrc, hscratch', hmarks', harch,
        h1, h2, h8, h9⟩ houtside)

end ShiTMCopyStageWithSkip
