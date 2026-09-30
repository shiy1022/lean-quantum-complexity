import «AMPUNI-replay-init-run»
import «AMPUNI-output-first-pass-replay-ready»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayPreface

open ShiTMLayoutMachine ShiTMRetainedTop

def liftEntryCfg (c : Cfg TopGam ShiTMOutputEntry.Label Sig) :
    Cfg TopGam ReplayLabel Sig :=
  liftCfg (ShiTMOutputEntry.liftStartedCfg c)

/-- A run of the checked retained-header/output-entry machine lifts through
both the delimiter-seeding and input-archive wrappers. -/
theorem run_entry_lift (steps : Nat)
    (c : Option (Cfg TopGam ShiTMOutputEntry.Label Sig)) :
    run^[steps] (c.map liftEntryCfg) =
      (ShiTMOutputEntry.run^[steps] c).map liftEntryCfg := by
  have h₁ := run_old steps (c.map ShiTMOutputEntry.liftStartedCfg)
  have h₂ := ShiTMOutputEntry.started_run_old steps c
  rw [h₂] at h₁
  change run^[steps]
      (c.map (fun x => liftCfg (ShiTMOutputEntry.liftStartedCfg x))) =
    (ShiTMOutputEntry.run^[steps] c).map
      (fun x => liftCfg (ShiTMOutputEntry.liftStartedCfg x))
  simpa only [Option.map_map, Function.comp_def] using h₁

end ShiTMReplayPreface
