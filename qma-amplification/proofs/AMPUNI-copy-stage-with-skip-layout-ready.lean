import «AMPUNI-copy-stage-with-skip-parser-lift»
import «AMPUNI-piece-expected-width»
import «AMPUNI-piece-sentinel»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController
  ShiTMPieceSchedule

/-- The concrete replay/program/mirror run reaches a parser configuration
whose table, mirror, work-stack, and output-accumulator fields are all ready
for the already-verified typed circuit pass. -/
theorem cycle_to_parser_layout (copy : Fin 3)
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = [])
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (harchive : V ShiTMReplayMarkSplit.archive =
      List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse)
    (hret : Retained n (F.wit n) (F.anc n) V)
    (h10 : V (.inl (.inl (10 : Fin 14))) = [])
    (h4 : V (.inl (.inl (4 : Fin 14))) = [Cell.delim])
    (h6 : V (.inl (.inl (6 : Fin 14))) = [])
    (h7 : V (.inl (.inl (7 : Fin 14))) = [])
    (h12 : V (.inl (.inl (12 : Fin 14))) = [])
    (hc0 : V (.inl (.inr (0 : Fin 2))) = [])
    (hc1 : V (.inl (.inr (1 : Fin 2))) = []) :
    ∃ (W T P : ∀ k, List (TopGam k)),
      run^[cycleSkipCost F n + ShiTMReplayTableClear.clearCost W + 1 +
        (scheduleCost n (F.wit n) (F.anc n) (program copy) + 1 + 1) +
        ((2 * (T (.inl (.inl (1 : Fin 14)))).length + 3) +
          (2 * (T (.inl (.inl (2 : Fin 14)))).length + 3) + 1)]
        (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
          (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (copyParserLabel copy
          (.inl (.inr .circuitHeader))), none, P⟩
      ∧ P ShiTMReplayReload.source =
          (ShiBQP.encCirc (F.circ n)).map bit
      ∧ P ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ P (.inl (.inl (0 : Fin 14))) = []
      ∧ P (.inl (.inl (1 : Fin 14))) =
          pieceCells Prod.fst (expectedPieces copy n (F.wit n) (F.anc n))
      ∧ P (.inl (.inl (2 : Fin 14))) =
          pieceCells Prod.snd (expectedPieces copy n (F.wit n) (F.anc n))
      ∧ P (.inl (.inl (3 : Fin 14))) = []
      ∧ P (.inl (.inl (4 : Fin 14))) = [Cell.delim]
      ∧ P (.inl (.inl (6 : Fin 14))) = []
      ∧ P (.inl (.inl (7 : Fin 14))) = []
      ∧ P (.inl (.inl (8 : Fin 14))) =
          (pieceCells Prod.fst
            (expectedPieces copy n (F.wit n) (F.anc n))).reverse ++
            [Cell.mirrorEnd]
      ∧ P (.inl (.inl (9 : Fin 14))) =
          (pieceCells Prod.snd
            (expectedPieces copy n (F.wit n) (F.anc n))).reverse ++
            [Cell.mirrorEnd]
      ∧ P (.inl (.inl (10 : Fin 14))) = []
      ∧ P (.inl (.inl (12 : Fin 14))) = []
      ∧ P (.inl (.inr (0 : Fin 2))) = []
      ∧ P (.inl (.inr (1 : Fin 2))) = []
      ∧ P (.inl (.inl (13 : Fin 14))) = V (.inl (.inl (13 : Fin 14)))
      ∧ Retained n (F.wit n) (F.anc n) P := by
  obtain ⟨W, U, T, P, hrun, _, htable, hPsource, hPscratch,
    hParchive, hP1, hP2, hP8, hP9, hP10, hPret, hPmarks, hstable⟩ :=
    cycle_to_parser_run copy F n V
      hsource hscratch hmarks harchive hret h10
  have hT1 : T (.inl (.inl (1 : Fin 14))) =
      pieceCells Prod.fst (expectedPieces copy n (F.wit n) (F.anc n)) := by
    exact congrArg Prod.fst htable
  have hT2 : T (.inl (.inl (2 : Fin 14))) =
      pieceCells Prod.snd (expectedPieces copy n (F.wit n) (F.anc n)) := by
    exact congrArg Prod.snd htable
  have hPstable (j : TopK) (hj : CopyStable j)
      (ho : OutsideWrites j)
      (hj10 : j ≠ .inl (.inl (10 : Fin 14))) : P j = V j :=
    hstable j hj ho hj10
  refine ⟨W, T, P, by simpa [copyParserLabel] using hrun,
    hPsource, hParchive, hPmarks, hP1.trans hT1, hP2.trans hT2,
    hPscratch, ?_, ?_, ?_, ?_, ?_, hP10, ?_, ?_, ?_, ?_, hPret⟩
  · exact (hPstable _ (by simp [CopyStable, ShiTMReplayTableClear.stack,
      ShiTMReplayTableClear.target]) (by simp [OutsideWrites])
      (by decide)).trans h4
  · exact (hPstable _ (by simp [CopyStable, ShiTMReplayTableClear.stack,
      ShiTMReplayTableClear.target]) (by simp [OutsideWrites])
      (by decide)).trans h6
  · exact (hPstable _ (by simp [CopyStable, ShiTMReplayTableClear.stack,
      ShiTMReplayTableClear.target]) (by simp [OutsideWrites])
      (by decide)).trans h7
  · rw [hP8, hT1]
  · rw [hP9, hT2]
  · exact (hPstable _ (by simp [CopyStable, ShiTMReplayTableClear.stack,
      ShiTMReplayTableClear.target]) (by simp [OutsideWrites])
      (by decide)).trans h12
  · exact (hPstable _ (by simp [CopyStable, ShiTMReplayTableClear.stack,
      ShiTMReplayTableClear.target]) (by simp [OutsideWrites])
      (by decide)).trans hc0
  · exact (hPstable _ (by simp [CopyStable, ShiTMReplayTableClear.stack,
      ShiTMReplayTableClear.target]) (by simp [OutsideWrites])
      (by decide)).trans hc1
  · exact hPstable _ (by simp [CopyStable, ShiTMReplayTableClear.stack,
      ShiTMReplayTableClear.target]) (by simp [OutsideWrites])
      (by decide)

end ShiTMCopyStageWithSkip
