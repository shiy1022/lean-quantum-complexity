import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMTypedTimeout

abbrev ClockK (K : Type) := K ⊕ Unit
abbrev ClockL (L : Type) := (L × Bool) ⊕ Unit

/-- Source stacks retain their individual alphabet; only the new fuel stack
is Boolean. This is the dependent-alphabet extension needed for `TopGam`. -/
abbrev ClockGam {K : Type} (Gam : K → Type) : ClockK K → Type
  | .inl k => Gam k
  | .inr _ => Bool

def tick {L : Type} (l : L) : ClockL L := .inl (l, false)
def exec {L : Type} (l : L) : ClockL L := .inl (l, true)
def timeout {L : Type} : ClockL L := .inr ()

def liftStk {K : Type} {Gam : K → Type} (fuel : List Bool)
    (S : ∀ k, List (Gam k)) : ∀ j, List (ClockGam Gam j)
  | .inl k => S k
  | .inr _ => fuel

def clockStmt {K L sig : Type} {Gam : K → Type} :
    Stmt Gam L sig → Stmt (ClockGam Gam) (ClockL L) (sig × Bool)
  | .push k f q => .push (.inl k) (fun w => f w.1) (clockStmt q)
  | .peek k f q => .peek (.inl k) (fun w x => (f w.1 x, w.2)) (clockStmt q)
  | .pop k f q => .pop (.inl k) (fun w x => (f w.1 x, w.2)) (clockStmt q)
  | .load f q => .load (fun w => (f w.1, w.2)) (clockStmt q)
  | .branch f q₁ q₂ =>
      .branch (fun w => f w.1) (clockStmt q₁) (clockStmt q₂)
  | .goto f => .load (fun w => (w.1, false))
      (.goto (fun w => tick (f w.1)))
  | .halt => .load (fun w => (w.1, false)) .halt

def clockMWith {K L sig : Type} {Gam : K → Type} [DecidableEq K]
    (M : L → Stmt Gam L sig)
    (onTimeout : Stmt (ClockGam Gam) (ClockL L) (sig × Bool)) :
    ClockL L → Stmt (ClockGam Gam) (ClockL L) (sig × Bool)
  | .inl (l, false) =>
      .pop (.inr ()) (fun w x => (w.1, x.isSome))
        (.branch Prod.snd (.goto (fun _ => exec l))
          (.goto (fun _ => timeout)))
  | .inl (l, true) => clockStmt (M l)
  | .inr _ => onTimeout

def liftCfg {K L sig : Type} {Gam : K → Type}
    (fuel : List Bool) (c : Cfg Gam L sig) :
    Cfg (ClockGam Gam) (ClockL L) (sig × Bool) :=
  { l := c.l.map tick
    var := (c.var, false)
    stk := liftStk fuel c.stk }

end ShiTMTypedTimeout
