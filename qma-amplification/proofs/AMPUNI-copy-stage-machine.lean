import «AMPUNI-replay-cycle-full-run»
import «AMPUNI-replay-table-clear-finite»
import «AMPUNI-piece-controller-frame-finish»
import «AMPUNI-mirror-init-both-run»
import «AMPUNI-retained-top-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStage

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Pre-skip control skeleton for the two remaining copies. The usable
copy-stage machine wraps this graph with `ShiTMCopyStageWithSkip`, inserting
the required replayed-header scan between replay and table clearing. -/
abbrev Label :=
  (Fin 3 × ShiTMReplayCycle.CycleLabel) ⊕
  ((Fin 3 × ShiTMReplayTableClear.Phase) ⊕
  ((Fin 3 × ShiTMPieceController.Label) ⊕
  ((Fin 3 × ShiTMMirrorInit.Phase) ⊕
  ((Fin 3 × TopLabel) ⊕ Unit))))

def cycleLabel (copy : Fin 3) (l : ShiTMReplayCycle.CycleLabel) : Label :=
  .inl (copy, l)
def clearLabel (copy : Fin 3) (l : ShiTMReplayTableClear.Phase) : Label :=
  .inr (.inl (copy, l))
def programLabel (copy : Fin 3) (l : ShiTMPieceController.Label) : Label :=
  .inr (.inr (.inl (copy, l)))
def mirrorLabel (copy : Fin 3) (l : ShiTMMirrorInit.Phase) : Label :=
  .inr (.inr (.inr (.inl (copy, l))))
def parserLabel (copy : Fin 3) (l : TopLabel) : Label :=
  .inr (.inr (.inr (.inr (.inl (copy, l)))))
def doneLabel : Label := .inr (.inr (.inr (.inr (.inr ()))))

def liftStmt {A : Type} (f : A → Label) :
    Stmt TopGam A Sig → Stmt TopGam Label Sig
  | .push k g q => .push k g (liftStmt f q)
  | .peek k g q => .peek k g (liftStmt f q)
  | .pop k g q => .pop k g (liftStmt f q)
  | .load g q => .load g (liftStmt f q)
  | .branch g q₁ q₂ => .branch g (liftStmt f q₁) (liftStmt f q₂)
  | .goto g => .goto (fun v => f (g v))
  | .halt => .halt

def machine : Label → Stmt TopGam Label Sig
  | .inl (copy, l) =>
      if l = ShiTMReplayCycle.restoreLabel true then
        .goto (fun _ => clearLabel copy .width)
      else liftStmt (cycleLabel copy) (ShiTMReplayCycle.machine l)
  | .inr (.inl (copy, l)) =>
      if l = .done then
        .goto (fun _ => programLabel copy (.dispatch copy 0))
      else liftStmt (clearLabel copy) (ShiTMReplayTableClear.machine l)
  | .inr (.inr (.inl (copy, l))) =>
      match l with
      | .finished _ => .goto (fun _ => mirrorLabel copy .startWidth)
      | _ => liftStmt (programLabel copy) (ShiTMPieceController.machine l)
  | .inr (.inr (.inr (.inl (copy, l)))) =>
      if l = .done then
        .goto (fun _ => parserLabel copy (.inl (.inr .circuitHeader)))
      else liftStmt (mirrorLabel copy) (ShiTMMirrorInit.machine l)
  | .inr (.inr (.inr (.inr (.inl (copy, l))))) =>
      if l = (.inl (.inr .exit) : TopLabel) then
        .goto (fun _ => if copy = 1 then
          cycleLabel 2 (ShiTMReplayCycle.splitLabel false) else doneLabel)
      else liftStmt (parserLabel copy) (topMachine l)
  | .inr (.inr (.inr (.inr (.inr ())))) => .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step machine)

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := ShiTMOutputEntry.finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Label
  main := cycleLabel 1 (ShiTMReplayCycle.splitLabel false)
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMCopyStage
