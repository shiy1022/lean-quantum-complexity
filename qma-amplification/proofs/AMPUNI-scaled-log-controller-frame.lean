import «AMPUNI-scaled-log-aux-embed»
import «AMPUNI-right-frame»
import «AMPUNI-state-reindex»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMScaledLogControllerFrame

variable {K W : Type} [DecidableEq K] {G : K → Type}

/-- Rearrange the preserved source state and loader parity into the state
shape used by the generic amplification controller. -/
def stateEquiv :
    (W × ShiTMUnaryLog.State) ≃
      (Option Bool × (Bool × W)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by
    intro x
    rcases x with ⟨w, v, parity⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨v, parity, w⟩
    rfl

def rawMachine (copies offset : Nat) :
    ShiTMUnaryLog.Label →
      Stmt (ShiTMRepeatController.Gam G)
        ShiTMUnaryLog.Label (W × ShiTMUnaryLog.State) :=
  ShiTMRightFrame.machine (E := G) (W := W)
    (ShiTMScaledLogAux.machine copies offset)

def machine (copies offset : Nat) :
    ShiTMUnaryLog.Label →
      Stmt (ShiTMRepeatController.Gam G)
        ShiTMUnaryLog.Label (Option Bool × (Bool × W)) :=
  ShiTMStateReindex.machine (stateEquiv (W := W))
    (rawMachine (G := G) (W := W) copies offset)

def cfg (S : ∀ j, List (G j)) (header : List Bool) (w : W)
    (c : Cfg ShiTMUnaryLog.Gam ShiTMUnaryLog.Label
      ShiTMUnaryLog.State) :
    Cfg (ShiTMRepeatController.Gam G)
      ShiTMUnaryLog.Label (Option Bool × (Bool × W)) :=
  ShiTMStateReindex.cfg (stateEquiv (W := W))
    (ShiTMRightFrame.cfg S w
      (ShiTMScaledLogAux.cfg header c))

/-- A loader run preserves every source-machine stack and the untouched
controller header bank, while its finite state carries the source state. -/
theorem run_frame (copies offset : Nat)
    (S : ∀ j, List (G j)) (header : List Bool) (w : W)
    (c : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
    ShiTMSubroutine.run
        (machine (G := G) (W := W) copies offset)
        (c.map (cfg S header w)) =
      ((ShiTMScaledLog.run copies offset) c).map
        (cfg S header w) := by
  let e := stateEquiv (W := W)
  let A := ShiTMScaledLogAux.machine copies offset
  let B := ShiTMRightFrame.machine (E := G) (W := W) A
  have hmap (c' : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
      c'.map (cfg S header w) =
        ((c'.map (ShiTMScaledLogAux.cfg header)).map
          (ShiTMRightFrame.cfg S w)).map
          (ShiTMStateReindex.cfg e) := by
    cases c' <;> rfl
  rw [hmap c, hmap ((ShiTMScaledLog.run copies offset) c)]
  change ShiTMSubroutine.run
      (ShiTMStateReindex.machine e B)
      (((c.map (ShiTMScaledLogAux.cfg header)).map
        (ShiTMRightFrame.cfg S w)).map
          (ShiTMStateReindex.cfg e)) = _
  rw [ShiTMStateReindex.run_frame,
    ShiTMRightFrame.run_frame,
    ShiTMScaledLogAux.run_frame]

theorem run_iter_frame (copies offset : Nat)
    (S : ∀ j, List (G j)) (header : List Bool) (w : W)
    (n : Nat) (c : Option (Cfg ShiTMUnaryLog.Gam
      ShiTMUnaryLog.Label ShiTMUnaryLog.State)) :
    (ShiTMSubroutine.run
      (machine (G := G) (W := W) copies offset))^[n]
        (c.map (cfg S header w)) =
      (((ShiTMScaledLog.run copies offset)^[n] c).map
        (cfg S header w)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply, run_frame]
      exact ih _

end ShiTMScaledLogControllerFrame
