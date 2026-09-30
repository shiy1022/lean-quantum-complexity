import «AMPUNI-polynomial-fuel-cost»
import «AMPUNI-stack-frame»
import «AMPUNI-state-frame»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMPolynomialFuelFrame
variable {K W : Type} [DecidableEq K] {G : K → Type}

abbrev Gam := ShiTMStackFrame.Gam ShiTMFuel.Gam G

def machine (d k : Nat) : ShiTMPolynomialFuel.Label d →
    Stmt (Gam (G := G)) (ShiTMPolynomialFuel.Label d) (ShiTMFuel.State × W) :=
  ShiTMStateFrame.machine (ShiTMStackFrame.machine (ShiTMPolynomialFuel.machine d k))

def cfg {d : Nat} (w : W) (S : ∀ j, List (G j)) (l : ShiTMPolynomialFuel.Label d)
    (xs tmp ctr fuel : List Bool) :
    Cfg (Gam (G := G)) (ShiTMPolynomialFuel.Label d) (ShiTMFuel.State × W) :=
  ShiTMStateFrame.cfg w (ShiTMStackFrame.cfg S (ShiTMPolynomialFuel.cfg l none xs tmp ctr fuel))

/-- The general fuel initializer preserves an arbitrary surrounding frame. -/
theorem fuel_run (d k : Nat) (w : W) (S : ∀ j, List (G j)) (xs : List Bool) :
    (ShiTMSubroutine.run (machine (G := G) (W := W) d k))^[
        1 + ShiTMPolynomialFuel.work d xs.length k]
      (some (cfg w S ShiTMPolynomialFuel.init xs [] [] [])) =
      some (cfg w S ShiTMPolynomialFuel.done xs [] []
        (List.replicate (k * (xs.length + 1) ^ (d + 1)) true)) := by
  have hf := ShiTMPolynomialFuel.fuel_run d k xs
  change (ShiTMStackFrame.run (ShiTMPolynomialFuel.machine d k))^[_] _ = _ at hf
  have hs := ShiTMStackFrame.run_iter_frame (ShiTMPolynomialFuel.machine d k) S
    (1 + ShiTMPolynomialFuel.work d xs.length k)
    (some (ShiTMPolynomialFuel.cfg ShiTMPolynomialFuel.init none xs [] [] []))
  rw [hf] at hs
  have hv := ShiTMStateFrame.run_iter_frame
    (ShiTMStackFrame.machine (E := G) (ShiTMPolynomialFuel.machine d k)) w
    (1 + ShiTMPolynomialFuel.work d xs.length k)
    ((some (ShiTMPolynomialFuel.cfg ShiTMPolynomialFuel.init none xs [] [] [])).map
      (ShiTMStackFrame.cfg S))
  change (ShiTMSubroutine.run (ShiTMStackFrame.machine
    (ShiTMPolynomialFuel.machine d k)))^[_] _ = _ at hs
  rw [hs] at hv
  exact hv

end ShiTMPolynomialFuelFrame
