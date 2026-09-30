import «AMPUNI-copy-stage-with-skip-machine»
import «AMPUNI-copy-stage-cycle-clear-step»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

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

theorem replay_to_skip_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
      (ShiTMReplayCycle.restoreLabel true))), v, S⟩) =
      some ⟨some (skipLabel copy 0), v, S⟩ := by
  simp [run, machine, oldLabel, skipLabel,
    ShiTMCopyStage.cycleLabel, step, stepAux]

theorem cycle_nonterminal_step (copy : Fin 3)
    (l : ShiTMReplayCycle.CycleLabel)
    (hl : l ≠ ShiTMReplayCycle.restoreLabel true)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy l)), v, S⟩) =
      (ShiTMReplayCycle.run (some ⟨some l, v, S⟩)).map
        (liftCfg (fun q => oldLabel (ShiTMCopyStage.cycleLabel copy q))) := by
  have h₁ := stepAux_liftStmt oldLabel
    (ShiTMCopyStage.liftStmt (ShiTMCopyStage.cycleLabel copy)
      (ShiTMReplayCycle.machine l)) v S
  have h₂ := ShiTMCopyStage.stepAux_liftStmt
    (ShiTMCopyStage.cycleLabel copy) (ShiTMReplayCycle.machine l) v S
  have h : stepAux
      (liftStmt oldLabel (ShiTMCopyStage.liftStmt
        (ShiTMCopyStage.cycleLabel copy) (ShiTMReplayCycle.machine l))) v S =
      liftCfg (fun q => oldLabel (ShiTMCopyStage.cycleLabel copy q))
        (stepAux (ShiTMReplayCycle.machine l) v S) := by
    rw [h₁, h₂]
    simp [liftCfg, ShiTMCopyStage.liftCfg, Option.map_map,
      Function.comp_def]
  simpa [run, machine, oldLabel, ShiTMCopyStage.cycleLabel,
    ShiTMCopyStage.machine, hl, ShiTMReplayCycle.run, step,
    liftStmt] using congrArg some h

theorem clear_nonterminal_step (copy : Fin 3)
    (p : ShiTMReplayTableClear.Phase) (hp : p ≠ .done)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (oldLabel (ShiTMCopyStage.clearLabel copy p)), v, S⟩) =
      (ShiTMReplayTableClear.run (some ⟨some p, v, S⟩)).map
        (liftCfg (fun q => oldLabel (ShiTMCopyStage.clearLabel copy q))) := by
  have h₁ := stepAux_liftStmt oldLabel
    (ShiTMCopyStage.liftStmt (ShiTMCopyStage.clearLabel copy)
      (ShiTMReplayTableClear.machine p)) v S
  have h₂ := ShiTMCopyStage.stepAux_liftStmt
    (ShiTMCopyStage.clearLabel copy) (ShiTMReplayTableClear.machine p) v S
  have h : stepAux
      (liftStmt oldLabel (ShiTMCopyStage.liftStmt
        (ShiTMCopyStage.clearLabel copy) (ShiTMReplayTableClear.machine p))) v S =
      liftCfg (fun q => oldLabel (ShiTMCopyStage.clearLabel copy q))
        (stepAux (ShiTMReplayTableClear.machine p) v S) := by
    rw [h₁, h₂]
    simp [liftCfg, ShiTMCopyStage.liftCfg, Option.map_map,
      Function.comp_def]
  simpa [run, machine, oldLabel, ShiTMCopyStage.clearLabel,
    ShiTMCopyStage.machine, hp, ShiTMReplayTableClear.run, step,
    liftStmt] using congrArg some h

theorem skip_nonterminal_step (copy : Fin 3)
    (p : ShiTMReplayHeaderSkip.Phase) (hp : p ≠ 4)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (skipLabel copy p), v, S⟩) =
      (ShiTMReplayHeaderSkip.run (some ⟨some p, v, S⟩)).map
        (liftCfg (skipLabel copy)) := by
  have h := stepAux_liftStmt (skipLabel copy)
    (ShiTMReplayHeaderSkip.machine p) v S
  simpa [run, machine, skipLabel, hp,
    ShiTMReplayHeaderSkip.run, step] using congrArg some h

theorem skip_to_clear_step (copy : Fin 3) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (skipLabel copy 4), v, S⟩) =
      some ⟨some (oldLabel
        (ShiTMCopyStage.clearLabel copy .width)), v, S⟩ := by
  simp [run, machine, skipLabel, oldLabel,
    ShiTMCopyStage.clearLabel, step, stepAux]

end ShiTMCopyStageWithSkip
