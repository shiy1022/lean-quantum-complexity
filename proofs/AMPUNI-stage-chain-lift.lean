import «AMPUNI-stage-chain-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMStageChain

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

/-- A tail dispatch state executes exactly its parameterized-controller step,
with only the outer label embedding changed. -/
theorem tail_dispatch_step (pc : ShiTMPieceController.PC) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (tailLabel (.dispatch 0 pc)), var := v, stk := S }) =
      (ShiTMPieceParam.runFor ShiTMPieceSchedule.tailProgram
        (some { l := some (.dispatch 0 pc), var := v, stk := S })).map
          (liftCfg tailLabel) := by
  simp [run, machine, tailLabel, step, ShiTMPieceParam.runFor,
    stepAux_liftStmt]

theorem tail_work_step (pc : ShiTMPieceController.PC)
    (atom : ShiTMPieceSchedule.Atom) (table : ShiTMPieceSchedule.Table)
    (phase : ShiTMPieceEntry.Control) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (tailLabel (.work 0 pc atom table phase)), var := v, stk := S }) =
      (ShiTMPieceParam.runFor ShiTMPieceSchedule.tailProgram
        (some { l := some (.work 0 pc atom table phase), var := v, stk := S })).map
          (liftCfg tailLabel) := by
  simp [run, machine, tailLabel, step, ShiTMPieceParam.runFor,
    stepAux_liftStmt]

theorem copy_dispatch_step (copy : Fin 3) (pc : ShiTMPieceController.PC)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some { l := some (copyLabel (.dispatch copy pc)), var := v, stk := S }) =
      (ShiTMPieceController.run
        (some { l := some (.dispatch copy pc), var := v, stk := S })).map
          (liftCfg copyLabel) := by
  simp [run, machine, copyLabel, step, ShiTMPieceController.run,
    stepAux_liftStmt]

theorem copy_work_step (copy : Fin 3) (pc : ShiTMPieceController.PC)
    (atom : ShiTMPieceSchedule.Atom) (table : ShiTMPieceSchedule.Table)
    (phase : ShiTMPieceEntry.Control) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (copyLabel (.work copy pc atom table phase)), var := v, stk := S }) =
      (ShiTMPieceController.run
        (some { l := some (.work copy pc atom table phase), var := v, stk := S })).map
          (liftCfg copyLabel) := by
  simp [run, machine, copyLabel, step, ShiTMPieceController.run,
    stepAux_liftStmt]

end ShiTMStageChain
