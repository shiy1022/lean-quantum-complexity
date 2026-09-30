import «AMPUNI-output-header-schedule»
import «AMPUNI-piece-entry-param-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry

abbrev PC := Fin 32

def nextPC (pc : PC) : PC :=
  ⟨(pc.val + 1) % 32, Nat.mod_lt _ (by decide)⟩

def commandAt : List Command → Nat → Option Command
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: cs, i + 1 => commandAt cs i

def source : Atom → Fin 4
  | .input => 0
  | .witness => 1
  | .ancilla => 2
  | .one => 0

inductive Label where
  | dispatch (pc : PC)
  | work (pc : PC) (atom : Atom) (phase : Control)
  | finished
deriving DecidableEq, Fintype

/-- Relabel the already-proved empty-terminated unary-copy subroutine. Its
unreachable top-level labels map to `finished`; active work labels remain local. -/
def liftWork (pc : PC) (atom : Atom) :
    Stmt TopGam EntryLabel Sig → Stmt TopGam Label Sig
  | .push k f q => .push k f (liftWork pc atom q)
  | .peek k f q => .peek k f (liftWork pc atom q)
  | .pop k f q => .pop k f (liftWork pc atom q)
  | .load f q => .load f (liftWork pc atom q)
  | .branch f q₁ q₂ =>
      .branch f (liftWork pc atom q₁) (liftWork pc atom q₂)
  | .goto f => .goto (fun v =>
      match f v with
      | .inl _ => .finished
      | .inr phase => .work pc atom phase)
  | .halt => .halt

/-- Fixed finite controller for the three amplified numeric headers. Scratch
stack 3 is reused by the unary-copy subroutine; stack 13 is the accumulator. -/
def machine : Label → Stmt TopGam Label Sig
  | .dispatch pc =>
      match commandAt program pc.val with
      | none => .goto (fun _ => .finished)
      | some .delimiter =>
          .push (.inl (.inl (13 : Fin 14))) (cst .delim)
            (.goto (fun _ => .dispatch (nextPC pc)))
      | some (.add .one) =>
          .push (.inl (.inl (13 : Fin 14))) (cst .mark)
            (.goto (fun _ => .dispatch (nextPC pc)))
      | some (.add atom) =>
          .goto (fun _ => .work pc atom .copy)
  | .work pc _atom .done =>
      .goto (fun _ => .dispatch (nextPC pc))
  | .work pc atom phase =>
      liftWork pc atom
        (machineAt (source atom) (13 : Fin 14) (.inr phase))
  | .finished => .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun cf => cf.bind (step machine)

end ShiTMOutputHeader
