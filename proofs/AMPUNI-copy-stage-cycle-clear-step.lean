import «AMPUNI-copy-stage-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStage

open ShiTMLayoutMachine ShiTMRetainedTop

def liftCfg {A : Type} (f : A → Label)
    (c : Cfg TopGam A Sig) : Cfg TopGam Label Sig :=
  { l := c.l.map f, var := c.var, stk := c.stk }

theorem stepAux_liftStmt {A : Type} (f : A → Label)
    (q : Stmt TopGam A Sig) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    stepAux (liftStmt f q) v S = liftCfg f (stepAux q v S) := by
  induction q generalizing v S with
  | push k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih v (Function.update S k (g v :: S k))
  | peek k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v (S k).head?) S
  | pop k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v (S k).head?) (Function.update S k (S k).tail)
  | load g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v) S
  | branch g q₁ q₂ ih₁ ih₂ =>
      simp only [liftStmt, stepAux]
      cases h : g v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto g => rfl
  | halt => rfl

theorem cycle_nonterminal_step (copy : Fin 3)
    (l : ShiTMReplayCycle.CycleLabel)
    (hl : l ≠ ShiTMReplayCycle.restoreLabel true)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (cycleLabel copy l), v, S⟩) =
      (ShiTMReplayCycle.run (some ⟨some l, v, S⟩)).map
        (liftCfg (cycleLabel copy)) := by
  have h := stepAux_liftStmt (cycleLabel copy)
    (ShiTMReplayCycle.machine l) v S
  simpa [run, machine, cycleLabel, hl,
    ShiTMReplayCycle.run, step] using congrArg some h

theorem cycle_terminal_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (cycleLabel copy
      (ShiTMReplayCycle.restoreLabel true)), v, S⟩) =
      some ⟨some (clearLabel copy .width), v, S⟩ := by
  simp [run, machine, cycleLabel, clearLabel, step, stepAux]

theorem clear_nonterminal_step (copy : Fin 3)
    (l : ShiTMReplayTableClear.Phase) (hl : l ≠ .done)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (clearLabel copy l), v, S⟩) =
      (ShiTMReplayTableClear.run (some ⟨some l, v, S⟩)).map
        (liftCfg (clearLabel copy)) := by
  have h := stepAux_liftStmt (clearLabel copy)
    (ShiTMReplayTableClear.machine l) v S
  simpa [run, machine, clearLabel, hl,
    ShiTMReplayTableClear.run, step] using congrArg some h

theorem clear_terminal_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (clearLabel copy .done), v, S⟩) =
      some ⟨some (programLabel copy (.dispatch copy 0)), v, S⟩ := by
  simp [run, machine, clearLabel, programLabel, step, stepAux]

end ShiTMCopyStage
