import «AMPUNI-copy-stage-with-skip-program-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- One finite machine restores the verifier, skips its four headers, clears
old tables, runs the copy-specific piece program, and reaches mirror setup. -/
theorem cycle_skip_clear_program_run (copy : Fin 3)
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
    ∃ (W U T : ∀ k, List (TopGam k)) (v' : Sig),
      run^[cycleSkipCost F n + ShiTMReplayTableClear.clearCost W + 1 +
        (scheduleCost n (F.wit n) (F.anc n) (program copy) + 1 + 1)]
        (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
          (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy
          .startWidth)), v', T⟩
      ∧ tableState T =
          runCommands n (F.wit n) (F.anc n) (program copy) (tableState U)
      ∧ U (ShiTMReplayTableClear.stack .width) = []
      ∧ U (ShiTMReplayTableClear.stack .base) = []
      ∧ Retained n (F.wit n) (F.anc n) T
      ∧ T ShiTMReplayReload.source =
          (ShiBQP.encCirc (F.circ n)).map bit
      ∧ T ShiTMReplayReload.scratch = []
      ∧ T ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ T (.inl (.inl (8 : Fin 14))) = []
      ∧ T (.inl (.inl (9 : Fin 14))) = []
      ∧ T (.inl (.inl (10 : Fin 14))) = []
      ∧ T ShiTMReplayMarkRestore.marks = []
      ∧ ∀ j, CopyStable j → OutsideWrites j → T j = V j := by
  obtain ⟨W, U, hclear, hUsource, hUscratch, hUmarks, hUarchive,
    hUwidth, hUbase, hU8, hU9, hretU, hU10, hUstable⟩ :=
    cycle_skip_clear_run copy F n V hsource hscratch hmarks harchive hret h10
  obtain ⟨T, v', hprogram, htables, hretT, hscratchT, hframe⟩ :=
    program_run_to_mirror copy n (F.wit n) (F.anc n) none U
      hretU hUscratch
  refine ⟨W, U, T, v', ?_, htables, hUwidth, hUbase,
    hretT, ?_, hscratchT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact iterTwo run
      (cycleSkipCost F n + ShiTMReplayTableClear.clearCost W + 1)
      (scheduleCost n (F.wit n) (F.anc n) (program copy) + 1 + 1)
      _ _ _ hclear hprogram
  · exact (hframe _ (by simp [OutsideWrites])).trans hUsource
  · exact (hframe _ (by simp [OutsideWrites])).trans hUarchive
  · exact (hframe _ (by simp [OutsideWrites])).trans hU8
  · exact (hframe _ (by simp [OutsideWrites])).trans hU9
  · exact (hframe _ (by simp [OutsideWrites])).trans hU10
  · exact (hframe _ (by simp [OutsideWrites])).trans hUmarks
  · intro j hstable houtside
    exact (hframe j houtside).trans (hUstable j hstable)

end ShiTMCopyStageWithSkip
