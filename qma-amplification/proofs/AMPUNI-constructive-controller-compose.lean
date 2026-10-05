import «AMPUNI-constructive-controller-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- Compose an integrated startup run with any checked run of the
embedded repetition controller. -/
theorem startup_then_controller
    (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (a t : Nat)
    (x : Option (Cfg (ShiTMRepeatController.Gam G)
      (Label L) (Option Bool × (Bool × W))))
    (c d : Cfg (ShiTMRepeatController.Gam G)
      (ShiTMRepeatController.Label L)
      (Option Bool × (Bool × W)))
    (hstart : (ShiTMSubroutine.run
      (machine p M entry terminal input output
        decodeInput decodeOutput encodeInput))^[a] x =
      some (ShiTMSubroutine.cfg controller c))
    (hcontroller : (ShiTMSubroutine.run
      (ShiTMRepeatController.machine M entry terminal
        input output decodeOutput encodeInput))^[t]
        (some c) = some d) :
    (ShiTMSubroutine.run
      (machine p M entry terminal input output
        decodeInput decodeOutput encodeInput))^[a + t] x =
      some (ShiTMSubroutine.cfg controller d) := by
  have hlift := controller_run_frame p M entry terminal
    input output decodeInput decodeOutput encodeInput t (some c)
  rw [hcontroller] at hlift
  rw [show a + t = t + a by omega,
    Function.iterate_add_apply, hstart]
  simpa using hlift

end ShiTMConstructiveIntegrated
