import «AMPUNI-scaled-log-controller-frame»
import «AMPUNI-scaled-log-body»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMScaledLogControllerFrame

variable {K W : Type} [DecidableEq K] {G : K → Type}

def liftMachine
    (M : ShiTMUnaryLog.Label →
      Stmt ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
        ShiTMUnaryLog.State) :
    ShiTMUnaryLog.Label →
      Stmt (ShiTMRepeatController.Gam G)
        ShiTMUnaryLog.Label (Option Bool × (Bool × W)) :=
  ShiTMStateReindex.machine (stateEquiv (W := W))
    (ShiTMRightFrame.machine (E := G) (W := W)
      (ShiTMScaledLogAux.liftMachine M))

theorem run_frame_any
    (M : ShiTMUnaryLog.Label →
      Stmt ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
        ShiTMUnaryLog.State)
    (S : ∀ j, List (G j)) (header : List Bool) (w : W)
    (c : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
    ShiTMSubroutine.run (liftMachine (G := G) (W := W) M)
        (c.map (cfg S header w)) =
      ((ShiTMSubroutine.run M) c).map (cfg S header w) := by
  let e := stateEquiv (W := W)
  let A := ShiTMScaledLogAux.liftMachine M
  let B := ShiTMRightFrame.machine (E := G) (W := W) A
  have hmap (c' : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
      c'.map (cfg S header w) =
        ((c'.map (ShiTMScaledLogAux.cfg header)).map
          (ShiTMRightFrame.cfg S w)).map
          (ShiTMStateReindex.cfg e) := by
    cases c' <;> rfl
  rw [hmap c, hmap ((ShiTMSubroutine.run M) c)]
  change ShiTMSubroutine.run
      (ShiTMStateReindex.machine e B)
      (((c.map (ShiTMScaledLogAux.cfg header)).map
        (ShiTMRightFrame.cfg S w)).map
          (ShiTMStateReindex.cfg e)) = _
  rw [ShiTMStateReindex.run_frame,
    ShiTMRightFrame.run_frame,
    ShiTMScaledLogAux.run_frame_any]

theorem run_iter_frame_any
    (M : ShiTMUnaryLog.Label →
      Stmt ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
        ShiTMUnaryLog.State)
    (S : ∀ j, List (G j)) (header : List Bool) (w : W)
    (n : Nat) (c : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
    (ShiTMSubroutine.run
      (liftMachine (G := G) (W := W) M))^[n]
        (c.map (cfg S header w)) =
      (((ShiTMSubroutine.run M)^[n] c).map
        (cfg S header w)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply, run_frame_any]
      exact ih _

end ShiTMScaledLogControllerFrame
