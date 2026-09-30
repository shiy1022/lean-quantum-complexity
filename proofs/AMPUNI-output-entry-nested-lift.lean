import «AMPUNI-output-entry-parser-lift»
import «AMPUNI-retained-nested-lift»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

def liftNestedCfg (H : Fin 4 → List Cell)
    (c : Cfg OuterGam OuterLabel Sig) : Cfg TopGam Label Sig :=
  liftCfg parserLabel (ShiTMRetainedTop.liftCfg H c)

private theorem map_nested (H : Fin 4 → List Cell)
    (c : Option (Cfg OuterGam OuterLabel Sig)) :
    c.map (liftNestedCfg H) =
      (c.map (ShiTMRetainedTop.liftCfg H)).map (liftCfg parserLabel) := by
  cases c <;> rfl

theorem nested_step_lift (H : Fin 4 → List Cell)
    (c : Option (Cfg OuterGam OuterLabel Sig)) :
    run (c.map (liftNestedCfg H)) =
      (nestedRun c).map (liftNestedCfg H) := by
  rw [map_nested, parser_step_option, ShiTMRetainedTop.topRun_lift]
  rw [← map_nested]

theorem nested_run_lift (H : Fin 4 → List Cell) (n : Nat)
    (c : Option (Cfg OuterGam OuterLabel Sig)) :
    run^[n] (c.map (liftNestedCfg H)) =
      (nestedRun^[n] c).map (liftNestedCfg H) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [nested_step_lift]
      exact ih _

end ShiTMOutputEntry
