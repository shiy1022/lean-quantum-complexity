import «AMPUNI-repeat-controller-step»
import «AMPUNI-repeat-body-embed»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- A whole source round runs inside the controller with the same time cost.
The controller does not inspect or alter any auxiliary stack before the
active terminal label is reached. -/
theorem run_body (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (hhalt : M terminal = .halt)
    (b : Bool) (A : Aux → List Bool)
    (n : Nat) (c : Option (Cfg G L (Option Bool × W)))
    (d : Cfg G L (Option Bool × W))
    (hd : d.l = some terminal)
    (hr : (ShiTMSubroutine.run M)^[n] c = some d) :
    (ShiTMSubroutine.run
      (machine M entry terminal input output decodeOutput encodeInput))^[n]
        ((c.map (ShiTMStackFrame.cfg A)).map (ShiTMSubroutine.cfg (body b))) =
      some (ShiTMSubroutine.cfg (body b) (ShiTMStackFrame.cfg A d)) := by
  have hf := ShiTMStackFrame.run_iter_frame (E := fun _ : Aux => Bool) M A n c
  change (ShiTMSubroutine.run (ShiTMStackFrame.machine M))^[n]
    (c.map (ShiTMStackFrame.cfg A)) =
      ((ShiTMSubroutine.run M)^[n] c).map (ShiTMStackFrame.cfg A) at hf
  rw [hr] at hf
  exact ShiTMSubroutine.run_to_terminal
    (ShiTMStackFrame.machine (E := fun _ : Aux => Bool) M)
    (machine M entry terminal input output decodeOutput encodeInput)
    (body b) terminal
    (by simp [ShiTMStackFrame.machine, ShiTMStackFrame.stmt, hhalt])
    (by intro l hl; simp [machine, body, hl, ShiTMStackFrame.machine])
    n _ _ (by simpa [ShiTMStackFrame.cfg] using hd) hf

end ShiTMRepeatController
