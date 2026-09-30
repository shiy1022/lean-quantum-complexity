import «AMPUNI-copy-stage-cycle-clear-step»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStage

open ShiTMLayoutMachine ShiTMRetainedTop

theorem mirror_nonterminal_step (copy : Fin 3)
    (l : ShiTMMirrorInit.Phase) (hl : l ≠ .done)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (mirrorLabel copy l), v, S⟩) =
      (ShiTMMirrorInit.run (some ⟨some l, v, S⟩)).map
        (liftCfg (mirrorLabel copy)) := by
  have h := stepAux_liftStmt (mirrorLabel copy)
    (ShiTMMirrorInit.machine l) v S
  simpa [run, machine, mirrorLabel, hl,
    ShiTMMirrorInit.run, step] using congrArg some h

theorem mirror_terminal_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (mirrorLabel copy .done), v, S⟩) =
      some ⟨some (parserLabel copy (.inl (.inr .circuitHeader))), v, S⟩ := by
  simp [run, machine, mirrorLabel, parserLabel, step, stepAux]

theorem parser_nonterminal_step (copy : Fin 3)
    (l : TopLabel) (hl : l ≠ (.inl (.inr .exit) : TopLabel))
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (parserLabel copy l), v, S⟩) =
      (topRun (some ⟨some l, v, S⟩)).map
        (liftCfg (parserLabel copy)) := by
  have h := stepAux_liftStmt (parserLabel copy) (topMachine l) v S
  simpa [run, machine, parserLabel, hl, topRun, step] using congrArg some h

theorem parser_terminal_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (parserLabel copy (.inl (.inr .exit))), v, S⟩) =
      some ⟨some (if copy = 1 then
        cycleLabel 2 (ShiTMReplayCycle.splitLabel false) else doneLabel), v, S⟩ := by
  simp [run, machine, parserLabel, step, stepAux]

end ShiTMCopyStage
