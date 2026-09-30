import «AMPUNI-replay-complete-cycle-state»
import «AMPUNI-output-entry-finite»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayCycle

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOutputEntry

/-- The first three replay routines share one finite control graph. The
terminal state of each routine performs a real transition into the next. -/
abbrev CycleLabel := Bool ⊕ (ShiTMReplayReload.ReloadLabel ⊕ Bool)

def splitLabel (b : Bool) : CycleLabel := .inl b
def reloadLabel (p : ShiTMReplayReload.ReloadLabel) : CycleLabel :=
  .inr (.inl p)
def restoreLabel (b : Bool) : CycleLabel := .inr (.inr b)

def liftStmt {A : Type} (f : A → CycleLabel) :
    Stmt TopGam A Sig → Stmt TopGam CycleLabel Sig
  | .push k g q => .push k g (liftStmt f q)
  | .peek k g q => .peek k g (liftStmt f q)
  | .pop k g q => .pop k g (liftStmt f q)
  | .load g q => .load g (liftStmt f q)
  | .branch g q₁ q₂ => .branch g (liftStmt f q₁) (liftStmt f q₂)
  | .goto g => .goto (fun v => f (g v))
  | .halt => .halt

def machine : CycleLabel → Stmt TopGam CycleLabel Sig
  | .inl false =>
      liftStmt splitLabel (ShiTMReplayMarkSplit.machine false)
  | .inl true => .goto (fun _ => reloadLabel 0)
  | .inr (.inl 0) =>
      liftStmt reloadLabel (ShiTMReplayReload.machine 0)
  | .inr (.inl 1) =>
      liftStmt reloadLabel (ShiTMReplayReload.machine 1)
  | .inr (.inl _) => .goto (fun _ => restoreLabel false)
  | .inr (.inr false) =>
      liftStmt restoreLabel (ShiTMReplayMarkRestore.machine false)
  | .inr (.inr true) => .halt

def run : Option (Cfg TopGam CycleLabel Sig) →
    Option (Cfg TopGam CycleLabel Sig) :=
  fun c => c.bind (step machine)

theorem split_done_step (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (splitLabel true), v, S⟩) =
      some ⟨some (reloadLabel 0), v, S⟩ := by
  simp [run, machine, splitLabel, reloadLabel, step, stepAux]

theorem reload_done_step (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (reloadLabel 2), v, S⟩) =
      some ⟨some (restoreLabel false), v, S⟩ := by
  simp [run, machine, reloadLabel, restoreLabel, step, stepAux]

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := CycleLabel
  main := splitLabel false
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMReplayCycle
