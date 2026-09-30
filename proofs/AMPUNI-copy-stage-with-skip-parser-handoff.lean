import «AMPUNI-copy-stage-with-skip-full-copy-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The first later-copy parser hands the same stacks directly to the second
copy's replay controller. -/
theorem copy1_to_copy2_step (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (copyParserLabel 1 (.inl (.inr .exit))), v, S⟩) =
      some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel 2
        (ShiTMReplayCycle.splitLabel false))), v, S⟩ := by
  simp [run, machine, liftStmt, copyParserLabel, oldLabel,
    ShiTMCopyStage.machine, ShiTMCopyStage.parserLabel,
    ShiTMCopyStage.cycleLabel, step, stepAux]

/-- The final copy's parser exits to the corrected controller's done label. -/
theorem copy2_to_done_step (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (copyParserLabel 2 (.inl (.inr .exit))), v, S⟩) =
      some ⟨some (oldLabel ShiTMCopyStage.doneLabel), v, S⟩ := by
  simp [run, machine, liftStmt, copyParserLabel, oldLabel,
    ShiTMCopyStage.machine, ShiTMCopyStage.parserLabel,
    ShiTMCopyStage.doneLabel, step, stepAux]

end ShiTMCopyStageWithSkip
