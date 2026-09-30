import «AMPUNI-stage-chain-lift»
import «AMPUNI-retained-nested-lift»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMStageChain

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Parser transitions in the stage-chain machine are exactly the original
retained-top-machine transitions, with their labels embedded. -/
theorem parser_step (l : TopLabel) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (parserLabel l), var := v, stk := S }) =
      (topRun (some { l := some l, var := v, stk := S })).map
        (liftCfg parserLabel) := by
  change some (stepAux (liftStmt parserLabel (topMachine l)) v S) =
    some (liftCfg parserLabel (stepAux (topMachine l) v S))
  rw [stepAux_liftStmt]

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

end ShiTMStageChain
