import «AMPUNI-repeat-loader-prep»
import «AMPUNI-scaled-log-controller-bank»
import «AMPUNI-repeat-controller-prefix»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMConstructiveIntegrated

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

abbrev Label (L : Type) :=
  ((ShiTMRepeatController.Label L ⊕ ShiTMUnaryLog.Label) ⊕ Fin 3)

def scan : Label L := .inr 0
def duplicate : Label L := .inr 1
def seed : Label L := .inr 2
def loader (l : ShiTMUnaryLog.Label) : Label L := .inl (.inr l)
def controller (l : ShiTMRepeatController.Label L) : Label L :=
  .inl (.inl l)

/-- All fixed-offset pushes fit inside a single TM2 statement step. -/
def pushFinal (k : Nat)
    (q : Stmt (ShiTMRepeatController.Gam G) (Label L)
      (Option Bool × (Bool × W))) :
    Stmt (ShiTMRepeatController.Gam G) (Label L)
      (Option Bool × (Bool × W)) :=
  match k with
  | 0 => q
  | k + 1 => .push (.inr ShiTMRepeatController.counter)
      (fun _ => true) (pushFinal k q)

/-- One program connects the raw unary-prefix scan, duplication of the
length header, scaled logarithmic counter construction, and the existing
multi-round verifier controller. -/
def machine (p : Polynomial ℕ)
    (M : L → Stmt G L (Option Bool × (Bool × W)))
    (entry terminal : L) (input output : K)
    (decodeInput : G input → Bool)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input) :
    Label L → Stmt (ShiTMRepeatController.Gam G) (Label L)
      (Option Bool × (Bool × W))
  | .inr i =>
      if i = 0 then
        .pop (.inl input) (fun v x => (x.map decodeInput, v.2))
          (.branch (fun v => v.1 == some true)
            (.push (.inr (ShiTMRepeatController.header false))
              (fun _ => true) (.goto (fun _ => scan)))
            (.branch (fun v => v.1 == some false)
              (.goto (fun _ => duplicate))
              .halt))
      else if i = 1 then
        ShiTMRepeatTransfer.duplicate
          (.inr (ShiTMRepeatController.header false))
          (.inr ShiTMRepeatController.scratch)
          (.inr (ShiTMRepeatController.header true))
          id id id duplicate seed
      else
        .push (.inr ShiTMRepeatController.scratch)
          (fun _ => true)
          (.goto (fun _ => loader (.scan false)))
  | .inl (.inr l) =>
      if l = .done then
        pushFinal (ShiTMScaledLog.scheduleOffset p)
          (.goto (fun _ => controller
            (ShiTMRepeatController.phase true .separator)))
      else
        ShiTMSubroutine.stmt loader
          (ShiTMScaledLogControllerFrame.machine
            (G := G) (W := W) p.natDegree
              (ShiTMScaledLog.scheduleOffset p) l)
  | .inl (.inl l) =>
      ShiTMSubroutine.stmt controller
        (ShiTMRepeatController.machine M entry terminal
          input output decodeOutput encodeInput l)

end ShiTMConstructiveIntegrated
