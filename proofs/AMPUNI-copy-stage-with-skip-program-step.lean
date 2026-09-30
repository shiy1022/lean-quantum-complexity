import «AMPUNI-copy-stage-with-skip-clear-run»
import «AMPUNI-copy-stage-program-step»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

theorem old_program_step (copy : Fin 3)
    (l : ShiTMPieceController.Label) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy l)), v, S⟩) =
      (ShiTMCopyStage.run
        (some ⟨some (ShiTMCopyStage.programLabel copy l), v, S⟩)).map
          (liftCfg oldLabel) := by
  have h := stepAux_liftStmt oldLabel
    (ShiTMCopyStage.machine (ShiTMCopyStage.programLabel copy l)) v S
  simpa [run, machine, oldLabel, ShiTMCopyStage.programLabel,
    ShiTMCopyStage.run, step] using congrArg some h

theorem program_nonterminal_step (copy : Fin 3)
    (l : ShiTMPieceController.Label)
    (hl : ∀ actual : Fin 3, l ≠ .finished actual)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy l)), v, S⟩) =
      (ShiTMPieceController.run (some ⟨some l, v, S⟩)).map
        (liftCfg (fun q => oldLabel (ShiTMCopyStage.programLabel copy q))) := by
  rw [old_program_step,
    ShiTMCopyStage.program_nonterminal_step copy l hl v S]
  cases hrun : ShiTMPieceController.run (some ⟨some l, v, S⟩) with
  | none => rfl
  | some c =>
      cases c with
      | mk q x T =>
          cases q <;> rfl

theorem program_terminal_step (copy actual : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
      (.finished actual))), v, S⟩) =
      some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy .startWidth)),
        v, S⟩ := by
  rw [old_program_step,
    ShiTMCopyStage.program_terminal_step copy actual v S]
  rfl

end ShiTMCopyStageWithSkip
