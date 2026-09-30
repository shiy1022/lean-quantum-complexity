import «AMPUNI-fanout-prepare-run»
import «AMPUNI-fanout-run»
import «AMPUNI-top-stack-frame»
import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2

namespace ShiTMFanoutStage
open ShiTMLayoutMachine ShiTMRetainedTop

abbrev Label := (Bool × ShiTMFanoutPrepare.Label) ⊕
  ((Bool × ShiTMFanout.Label) ⊕ Option (Fin 3))
def prepLabel (second : Bool) (l : ShiTMFanoutPrepare.Label) : Label := .inl (second, l)
def emitLabel (second : Bool) (l : ShiTMFanout.Label) : Label := .inr (.inl (second, l))
def cleanLabel (k : Fin 3) : Label := .inr (.inr (some k))
def finished : Label := .inr (.inr none)

def emitter : ShiTMFanout.Label → Stmt TopGam ShiTMFanout.Label Sig :=
  ShiTMTopFrame.machine ShiTMFanout.machine

def afterClean (k : Fin 3) : Label :=
  if k = 0 then cleanLabel 1 else if k = 1 then cleanLabel 2 else finished

/-- Both fanouts, including register preparation between them and final work
register cleanup. No circuit/archive/output data is used as temporary storage. -/
def machine : Label → Stmt TopGam Label Sig
  | .inl (second, .finished) => .goto (fun _ => emitLabel second (.copy 0))
  | .inl (second, l) => ShiTMSubroutine.stmt (prepLabel second) (ShiTMFanoutPrepare.machine second l)
  | .inr (.inl (second, .finished)) =>
      .goto (fun _ => if second then cleanLabel 0 else prepLabel true (.clear 0))
  | .inr (.inl (second, l)) => ShiTMSubroutine.stmt (emitLabel second) (emitter l)
  | .inr (.inr (some k)) => .pop (ShiTMFanoutPrepare.port k) pop
      (.branch isSome (.goto (fun _ => cleanLabel k)) (.goto (fun _ => afterClean k)))
  | .inr (.inr none) => .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMFanoutPrepare.source 0
  k₁ := .inl ShiTMFanout.output
  Γ := TopGam
  Λ := Label
  main := prepLabel false (.clear 0)
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem prep_run_lift (second : Bool) (steps : Nat)
    (c : Option (Cfg TopGam ShiTMFanoutPrepare.Label Sig))
    (d : Cfg TopGam ShiTMFanoutPrepare.Label Sig)
    (hd : d.l = some .finished) (hr : (ShiTMFanoutPrepare.run second)^[steps] c = some d) :
    run^[steps] (c.map (ShiTMSubroutine.cfg (prepLabel second))) =
      some (ShiTMSubroutine.cfg (prepLabel second) d) := by
  apply ShiTMSubroutine.run_to_terminal (ShiTMFanoutPrepare.machine second)
    machine (prepLabel second) .finished rfl ?_ steps c d hd hr
  intro l hl
  cases l <;> simp_all [machine, prepLabel]

theorem emit_run_lift (second : Bool) (steps : Nat)
    (c : Option (Cfg TopGam ShiTMFanout.Label Sig))
    (d : Cfg TopGam ShiTMFanout.Label Sig)
    (hd : d.l = some .finished) (hr : (ShiTMSubroutine.run emitter)^[steps] c = some d) :
    run^[steps] (c.map (ShiTMSubroutine.cfg (emitLabel second))) =
      some (ShiTMSubroutine.cfg (emitLabel second) d) := by
  apply ShiTMSubroutine.run_to_terminal emitter machine (emitLabel second)
    .finished rfl ?_ steps c d hd hr
  intro l hl
  cases l <;> simp_all [machine, emitLabel]

theorem prep_handoff (second : Bool) (v : Sig) (S : ∀ j, List (TopGam j)) :
    run^[1] (some ⟨some (prepLabel second .finished), v, S⟩) =
      some ⟨some (emitLabel second (.copy 0)), v, S⟩ := by rfl

theorem emit_handoff (second : Bool) (v : Sig) (S : ∀ j, List (TopGam j)) :
    run^[1] (some ⟨some (emitLabel second .finished), v, S⟩) =
      some ⟨some (if second then cleanLabel 0 else prepLabel true (.clear 0)), v, S⟩ := by rfl

end ShiTMFanoutStage
