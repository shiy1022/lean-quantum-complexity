import «AMPUNI-replay-preface-first-pass»
import «AMPUNI-copy-stage-with-skip-two-copy-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCompleteController

open ShiTMLayoutMachine ShiTMRetainedTop

/-- One finite control graph joins the archived-input first pass to the two
later copy-specific passes. The first-pass parser exit is redirected to the
copy-1 replay entry; the copy-2 done label remains the terminal state. -/
abbrev Label := ShiTMReplayPreface.ReplayLabel ⊕
  ShiTMCopyStageWithSkip.Label

def firstLabel (l : ShiTMReplayPreface.ReplayLabel) : Label := .inl l
def copyLabel (l : ShiTMCopyStageWithSkip.Label) : Label := .inr l

def firstExit : ShiTMReplayPreface.ReplayLabel :=
  ShiTMReplayPreface.oldLabel
    (ShiTMOutputEntry.oldLabel
      (ShiTMOutputEntry.parserLabel (.inl (.inr .exit))))

def copy1Entry : ShiTMCopyStageWithSkip.Label :=
  ShiTMCopyStageWithSkip.oldLabel
    (ShiTMCopyStage.cycleLabel 1
      (ShiTMReplayCycle.splitLabel false))

def liftStmt {A : Type} (f : A → Label) :
    Stmt TopGam A Sig → Stmt TopGam Label Sig
  | .push k g q => .push k g (liftStmt f q)
  | .peek k g q => .peek k g (liftStmt f q)
  | .pop k g q => .pop k g (liftStmt f q)
  | .load g q => .load g (liftStmt f q)
  | .branch g q₁ q₂ => .branch g (liftStmt f q₁) (liftStmt f q₂)
  | .goto g => .goto (fun v => f (g v))
  | .halt => .halt

noncomputable def machine : Label → Stmt TopGam Label Sig := by
  classical
  intro l
  cases l with
  | inl l =>
      exact if l = firstExit then .goto (fun _ => copyLabel copy1Entry)
        else liftStmt firstLabel (ShiTMReplayPreface.machine l)
  | inr l =>
      exact liftStmt copyLabel (ShiTMCopyStageWithSkip.machine l)

noncomputable def run : Option (Cfg TopGam Label Sig) →
    Option (Cfg TopGam Label Sig) :=
  fun c => c.bind (step machine)

noncomputable def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := ShiTMOutputEntry.finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Label
  main := firstLabel ShiTMReplayPreface.copyLabel
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMCompleteController
