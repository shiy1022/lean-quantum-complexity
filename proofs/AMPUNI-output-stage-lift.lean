import «AMPUNI-output-stage-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputStage

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

theorem stage_step (l : ShiTMStageChain.Label) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (stageLabel l), var := v, stk := S }) =
      (ShiTMStageChain.run (some { l := some l, var := v, stk := S })).map
        (liftCfg stageLabel) := by
  change some (stepAux (liftStmt stageLabel (ShiTMStageChain.machine l)) v S) =
    some (liftCfg stageLabel (stepAux (ShiTMStageChain.machine l) v S))
  rw [stepAux_liftStmt]

theorem stage_step_option
    (c : Option (Cfg TopGam ShiTMStageChain.Label Sig)) :
    run (c.map (liftCfg stageLabel)) =
      (ShiTMStageChain.run c).map (liftCfg stageLabel) := by
  cases c with
  | none => rfl
  | some cfg =>
      cases cfg with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l => simpa [liftCfg] using stage_step l v S

theorem stage_run_lift (n : Nat)
    (c : Option (Cfg TopGam ShiTMStageChain.Label Sig)) :
    run^[n] (c.map (liftCfg stageLabel)) =
      (ShiTMStageChain.run^[n] c).map (liftCfg stageLabel) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [stage_step_option]
      exact ih _

end ShiTMOutputStage
