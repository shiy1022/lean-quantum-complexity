import «AMPUNI-fuel-run»
import «AMPUNI-stack-frame»
import «AMPUNI-state-frame»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFuelFrame
variable {K W : Type} [DecidableEq K] {G : K → Type}

abbrev Gam := ShiTMStackFrame.Gam ShiTMFuel.Gam G

def machine (k : Nat) : ShiTMFuel.Label → Stmt (Gam (G := G)) ShiTMFuel.Label
    (ShiTMFuel.State × W) :=
  ShiTMStateFrame.machine (ShiTMStackFrame.machine (ShiTMFuel.machine k))

def cfg (w : W) (S : ∀ j, List (G j)) (l : ShiTMFuel.Label)
    (xs tmp ctr fuel : List Bool) : Cfg (Gam (G := G)) ShiTMFuel.Label (ShiTMFuel.State × W) :=
  ShiTMStateFrame.cfg w (ShiTMStackFrame.cfg S (ShiTMFuel.cfg l none xs tmp ctr fuel))

/-- The fuel initializer can run beside arbitrary existing work stacks and
finite state, preserving them exactly and without any time overhead. -/
theorem fuel_run (k : Nat) (w : W) (S : ∀ j, List (G j)) (xs : List Bool) :
    (ShiTMSubroutine.run (machine (G := G) (W := W) k))^[(xs.length+2)*(2*xs.length+3)+1]
      (some (cfg w S .init xs [] [] [])) =
      some (cfg w S .done xs [] [] (List.replicate (k*(xs.length+1)^2) true)) := by
  have hf := ShiTMFuel.fuel_run k xs
  change (ShiTMStackFrame.run (ShiTMFuel.machine k))^[_] _ = _ at hf
  have hs := ShiTMStackFrame.run_iter_frame (ShiTMFuel.machine k) S
    ((xs.length+2)*(2*xs.length+3)+1) (some (ShiTMFuel.cfg .init none xs [] [] []))
  rw [hf] at hs
  have hv := ShiTMStateFrame.run_iter_frame
    (ShiTMStackFrame.machine (E := G) (ShiTMFuel.machine k)) w
    ((xs.length+2)*(2*xs.length+3)+1)
    ((some (ShiTMFuel.cfg .init none xs [] [] [])).map (ShiTMStackFrame.cfg S))
  change (ShiTMSubroutine.run (ShiTMStackFrame.machine (ShiTMFuel.machine k)))^[_] _ = _ at hs
  rw [hs] at hv
  exact hv

end ShiTMFuelFrame
