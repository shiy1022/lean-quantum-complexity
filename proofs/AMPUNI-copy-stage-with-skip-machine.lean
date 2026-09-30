import «AMPUNI-copy-stage-machine»
import «AMPUNI-replay-header-skip-four-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The copy-stage skeleton is wrapped with a header-skip phase. At replay
completion, this wrapper consumes the four restored unary headers without
adding to the already-retained counts, then resumes the table-clear phase. -/
abbrev Label := ShiTMCopyStage.Label ⊕
  (Fin 3 × ShiTMReplayHeaderSkip.Phase)

def oldLabel (l : ShiTMCopyStage.Label) : Label := .inl l
def skipLabel (copy : Fin 3) (p : ShiTMReplayHeaderSkip.Phase) : Label :=
  .inr (copy, p)

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
  | .inl (.inl (copy, l)) =>
      if l = ShiTMReplayCycle.restoreLabel true then
        .goto (fun _ => skipLabel copy 0)
      else liftStmt oldLabel
        (ShiTMCopyStage.machine (ShiTMCopyStage.cycleLabel copy l))
  | .inl l => liftStmt oldLabel (ShiTMCopyStage.machine l)
  | .inr (copy, p) =>
      if p = 4 then
        .goto (fun _ => oldLabel
          (ShiTMCopyStage.clearLabel copy .width))
      else liftStmt (skipLabel copy) (ShiTMReplayHeaderSkip.machine p)

def run : Option (Cfg TopGam Label Sig) →
    Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step machine)

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := ShiTMOutputEntry.finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Label
  main := oldLabel (ShiTMCopyStage.cycleLabel 1
    (ShiTMReplayCycle.splitLabel false))
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMCopyStageWithSkip
