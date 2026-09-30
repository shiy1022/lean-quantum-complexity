import «AMPUNI-output-entry-machine»
import «AMPUNI-output-stage-lift»
import «AMPUNI-stage-chain-parser-lift»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

def parserLabel (l : TopLabel) : Label :=
  bodyLabel (ShiTMOutputStage.stageLabel (ShiTMStageChain.parserLabel l))

theorem parser_step (l : TopLabel) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (parserLabel l), var := v, stk := S }) =
      (topRun (some { l := some l, var := v, stk := S })).map
        (liftCfg parserLabel) := by
  change some (stepAux
    (liftStmt bodyLabel
      (ShiTMOutputStage.liftStmt ShiTMOutputStage.stageLabel
        (ShiTMStageChain.liftStmt ShiTMStageChain.parserLabel
          (topMachine l)))) v S) =
      some (liftCfg parserLabel (stepAux (topMachine l) v S))
  rw [stepAux_liftStmt, ShiTMOutputStage.stepAux_liftStmt,
    ShiTMStageChain.stepAux_liftStmt]
  cases h : stepAux (topMachine l) v S with
  | mk label value T =>
      cases label <;> rfl

theorem parser_step_option (c : Option (Cfg TopGam TopLabel Sig)) :
    run (c.map (liftCfg parserLabel)) =
      (topRun c).map (liftCfg parserLabel) := by
  cases c with
  | none => rfl
  | some cfg =>
      cases cfg with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l => simpa [liftCfg] using parser_step l v S

theorem parser_run_lift (n : Nat)
    (c : Option (Cfg TopGam TopLabel Sig)) :
    run^[n] (c.map (liftCfg parserLabel)) =
      (topRun^[n] c).map (liftCfg parserLabel) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [parser_step_option]
      exact ih _

end ShiTMOutputEntry
