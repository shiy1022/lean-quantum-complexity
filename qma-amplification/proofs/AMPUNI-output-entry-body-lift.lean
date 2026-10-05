import «AMPUNI-output-entry-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

theorem body_step_option
    (c : Option (Cfg TopGam ShiTMOutputStage.Label Sig)) :
    run (c.map (liftCfg bodyLabel)) =
      (ShiTMOutputStage.run c).map (liftCfg bodyLabel) := by
  cases c with
  | none => rfl
  | some cfg =>
      cases cfg with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l => simpa [liftCfg] using body_step l v S

theorem body_run_lift (n : Nat)
    (c : Option (Cfg TopGam ShiTMOutputStage.Label Sig)) :
    run^[n] (c.map (liftCfg bodyLabel)) =
      (ShiTMOutputStage.run^[n] c).map (liftCfg bodyLabel) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [body_step_option]
      exact ih _

end ShiTMOutputEntry
