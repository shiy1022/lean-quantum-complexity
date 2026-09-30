import «AMPUNI-copy-stage-mirror-parser-step»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStage

open ShiTMLayoutMachine ShiTMRetainedTop

theorem program_nonterminal_step (copy : Fin 3)
    (l : ShiTMPieceController.Label)
    (hl : ∀ actual : Fin 3, l ≠ .finished actual)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (programLabel copy l), v, S⟩) =
      (ShiTMPieceController.run (some ⟨some l, v, S⟩)).map
        (liftCfg (programLabel copy)) := by
  cases l with
  | top l =>
      have h := stepAux_liftStmt (programLabel copy)
        (ShiTMPieceController.machine (.top l)) v S
      simpa [run, machine, programLabel,
        ShiTMPieceController.run, step] using congrArg some h
  | dispatch actual pc =>
      have h := stepAux_liftStmt (programLabel copy)
        (ShiTMPieceController.machine (.dispatch actual pc)) v S
      simpa [run, machine, programLabel,
        ShiTMPieceController.run, step] using congrArg some h
  | work actual pc atom table phase =>
      have h := stepAux_liftStmt (programLabel copy)
        (ShiTMPieceController.machine (.work actual pc atom table phase)) v S
      simpa [run, machine, programLabel,
        ShiTMPieceController.run, step] using congrArg some h
  | finished actual =>
      exact False.elim (hl actual rfl)

theorem program_terminal_step (copy actual : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (programLabel copy (.finished actual)), v, S⟩) =
      some ⟨some (mirrorLabel copy .startWidth), v, S⟩ := by
  simp [run, machine, programLabel, mirrorLabel, step, stepAux]

end ShiTMCopyStage
