import «AMPUNI-copy-stage-with-skip-cycle-run»
import «AMPUNI-replay-table-clear-all-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Stacks untouched by replay, header skipping, and old-table clearing. -/
def CopyStable (j : TopK) : Prop :=
  j ≠ ShiTMReplayReload.source ∧
  j ≠ ShiTMReplayReload.scratch ∧
  j ≠ ShiTMReplayMarkRestore.marks ∧
  j ≠ ShiTMReplayReload.archive ∧
  j ≠ ShiTMReplayTableClear.stack .width ∧
  j ≠ ShiTMReplayTableClear.stack .base ∧
  j ≠ ShiTMReplayTableClear.stack .widthMirror ∧
  j ≠ ShiTMReplayTableClear.stack .baseMirror

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem clear_to_program_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel
      (ShiTMCopyStage.clearLabel copy .done)), v, S⟩) =
      some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
        (.dispatch copy 0))), v, S⟩ := by
  simp [run, machine, oldLabel, ShiTMCopyStage.clearLabel,
    ShiTMCopyStage.programLabel, ShiTMCopyStage.machine,
    liftStmt, step, stepAux]

/-- The corrected finite copy-stage machine reaches the piece-program entry.
Replay and header skipping expose the original circuit; clearing empties all
four old width/base tables without modifying the circuit or retained archive. -/
theorem cycle_skip_clear_run (copy : Fin 3)
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = [])
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (harchive : V ShiTMReplayMarkSplit.archive =
      List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse)
    (hret : ShiTMPieceController.Retained
      n (F.wit n) (F.anc n) V)
    (h10 : V (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (W U : ∀ k, List (TopGam k)),
      run^[cycleSkipCost F n + ShiTMReplayTableClear.clearCost W + 1]
        (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
          (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
          (.dispatch copy 0))), none, U⟩
      ∧ U ShiTMReplayReload.source =
          (ShiBQP.encCirc (F.circ n)).map bit
      ∧ U ShiTMReplayReload.scratch = []
      ∧ U ShiTMReplayMarkRestore.marks = []
      ∧ U ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ U (ShiTMReplayTableClear.stack .width) = []
      ∧ U (ShiTMReplayTableClear.stack .base) = []
      ∧ U (ShiTMReplayTableClear.stack .widthMirror) = []
      ∧ U (ShiTMReplayTableClear.stack .baseMirror) = []
      ∧ ShiTMPieceController.Retained n (F.wit n) (F.anc n) U
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ ∀ j, CopyStable j → U j = V j := by
  obtain ⟨W, hcycle, hWsource, hWscratch, hWmarks, hWarchive,
    hWframe⟩ :=
    cycle_skip_run copy F n V hsource hscratch hmarks harchive
  obtain ⟨U, hclear, hwidth, hbase, hwm, hbm, hframe⟩ :=
    ShiTMReplayTableClear.clear_all_run (some Cell.delim) W
  have hclear' : run^[ShiTMReplayTableClear.clearCost W]
      (some ⟨some (oldLabel (ShiTMCopyStage.clearLabel copy .width)),
        some Cell.delim, W⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.clearLabel copy .done)),
          none, U⟩ := by
    simpa [liftCfg, oldLabel, ShiTMCopyStage.clearLabel] using
      clear_run_lift copy _
        (some ⟨some ShiTMReplayTableClear.Phase.width,
          some Cell.delim, W⟩)
        ⟨some ShiTMReplayTableClear.Phase.done, none, U⟩ rfl hclear
  have hprogram : run^[1]
      (some ⟨some (oldLabel (ShiTMCopyStage.clearLabel copy .done)),
        none, U⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
          (.dispatch copy 0))), none, U⟩ := by
    simpa using clear_to_program_step copy none U
  refine ⟨W, U, ?_, ?_, ?_, ?_, ?_, hwidth, hbase, hwm, hbm,
    ?_, ?_, ?_⟩
  · have h₁ := iterTwo run (cycleSkipCost F n)
      (ShiTMReplayTableClear.clearCost W) _ _ _ hcycle hclear'
    exact iterTwo run
      (cycleSkipCost F n + ShiTMReplayTableClear.clearCost W) 1
      _ _ _ h₁ hprogram
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
      hWsource
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
      hWscratch
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
      hWmarks
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
      hWarchive
  · rcases hret with ⟨h0, h1, h2⟩
    exact ⟨
      (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
        ((hWframe _ (by decide) (by decide) (by decide) (by decide)).trans h0),
      (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
        ((hWframe _ (by decide) (by decide) (by decide) (by decide)).trans h1),
      (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
        ((hWframe _ (by decide) (by decide) (by decide) (by decide)).trans h2)⟩
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide)).trans
      ((hWframe _ (by decide) (by decide) (by decide) (by decide)).trans h10)
  · intro j hj
    rcases hj with ⟨hsrc, hscratch', hmarks', harch,
      hwidth', hbase', hwm', hbm'⟩
    exact (hframe j hwidth' hbase' hwm' hbm').trans
      (hWframe j hsrc hscratch' hmarks' harch)

end ShiTMCopyStageWithSkip
