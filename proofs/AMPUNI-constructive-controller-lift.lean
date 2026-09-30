import «AMPUNI-constructive-loader-bank»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- Every controller run is an exact run of the integrated finite program
after the prefix loader has entered the controller's body label. -/
theorem controller_run_frame
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (t : Nat)
    (c : Option (Cfg (ShiTMRepeatController.Gam G)
      (ShiTMRepeatController.Label L)
      (Option Bool × (Bool × W)))) :
    (ShiTMSubroutine.run
      (machine p M entry terminal input output
        decodeInput decodeOutput encodeInput))^[t]
      (c.map (ShiTMSubroutine.cfg controller)) =
    ((ShiTMSubroutine.run
      (ShiTMRepeatController.machine M entry terminal
        input output decodeOutput encodeInput))^[t] c).map
      (ShiTMSubroutine.cfg controller) := by
  exact ShiTMSubroutine.run_iter_lift
    (ShiTMRepeatController.machine M entry terminal
      input output decodeOutput encodeInput)
    (machine p M entry terminal input output
      decodeInput decodeOutput encodeInput)
    controller (by intro l; rfl) t c

end ShiTMConstructiveIntegrated
