import «AMPUNI-complete-controller»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCompleteController

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

theorem first_nonterminal_step (l : ShiTMReplayPreface.ReplayLabel)
    (hl : l ≠ firstExit) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (firstLabel l), v, S⟩) =
      (ShiTMReplayPreface.run (some ⟨some l, v, S⟩)).map
        (liftCfg firstLabel) := by
  have h := stepAux_liftStmt firstLabel
    (ShiTMReplayPreface.machine l) v S
  simpa [run, machine, firstLabel, hl,
    ShiTMReplayPreface.run, step] using congrArg some h

theorem first_exit_step (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (firstLabel firstExit), v, S⟩) =
      some ⟨some (copyLabel copy1Entry), v, S⟩ := by
  simp [run, machine, firstLabel, step, stepAux]

theorem copy_step (l : ShiTMCopyStageWithSkip.Label)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (copyLabel l), v, S⟩) =
      (ShiTMCopyStageWithSkip.run (some ⟨some l, v, S⟩)).map
        (liftCfg copyLabel) := by
  have h := stepAux_liftStmt copyLabel
    (ShiTMCopyStageWithSkip.machine l) v S
  simpa [run, machine, copyLabel,
    ShiTMCopyStageWithSkip.run, step] using congrArg some h

theorem copy_step_option
    (c : Option (Cfg TopGam ShiTMCopyStageWithSkip.Label Sig)) :
    run (c.map (liftCfg copyLabel)) =
      (ShiTMCopyStageWithSkip.run c).map (liftCfg copyLabel) := by
  cases c with
  | none => rfl
  | some cfg =>
      cases cfg with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l => simpa [liftCfg] using copy_step l v S

theorem copy_run_lift (n : Nat)
    (c : Option (Cfg TopGam ShiTMCopyStageWithSkip.Label Sig)) :
    run^[n] (c.map (liftCfg copyLabel)) =
      (ShiTMCopyStageWithSkip.run^[n] c).map (liftCfg copyLabel) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [copy_step_option]
      exact ih _

end ShiTMCompleteController
