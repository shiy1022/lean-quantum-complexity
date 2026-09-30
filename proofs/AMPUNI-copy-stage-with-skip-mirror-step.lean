import «AMPUNI-copy-stage-with-skip-program-chain»
import «AMPUNI-copy-stage-mirror-parser-step»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

theorem old_mirror_step (copy : Fin 3)
    (p : ShiTMMirrorInit.Phase) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy p)), v, S⟩) =
      (ShiTMCopyStage.run
        (some ⟨some (ShiTMCopyStage.mirrorLabel copy p), v, S⟩)).map
          (liftCfg oldLabel) := by
  have h := stepAux_liftStmt oldLabel
    (ShiTMCopyStage.machine (ShiTMCopyStage.mirrorLabel copy p)) v S
  simpa [run, machine, oldLabel, ShiTMCopyStage.mirrorLabel,
    ShiTMCopyStage.run, step] using congrArg some h

theorem mirror_nonterminal_step (copy : Fin 3)
    (p : ShiTMMirrorInit.Phase) (hp : p ≠ .done)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy p)), v, S⟩) =
      (ShiTMMirrorInit.run (some ⟨some p, v, S⟩)).map
        (liftCfg (fun q => oldLabel (ShiTMCopyStage.mirrorLabel copy q))) := by
  rw [old_mirror_step,
    ShiTMCopyStage.mirror_nonterminal_step copy p hp v S]
  cases hrun : ShiTMMirrorInit.run (some ⟨some p, v, S⟩) with
  | none => rfl
  | some c =>
      cases c with
      | mk q x T => cases q <;> rfl

theorem mirror_terminal_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy .done)),
      v, S⟩) =
      some ⟨some (oldLabel (ShiTMCopyStage.parserLabel copy
        (.inl (.inr .circuitHeader)))), v, S⟩ := by
  rw [old_mirror_step,
    ShiTMCopyStage.mirror_terminal_step copy v S]
  rfl

end ShiTMCopyStageWithSkip
