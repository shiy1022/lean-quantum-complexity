import «AMPUNI-payload-copy-stage»
import «AMPUNI-prepared-readout»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMPayloadSuffix
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev CopyLabel := ShiTMPayloadCopyStage.Label
def copyTerminal : CopyLabel := ShiTMPayloadCopyStage.payloadLabel (some (.inr .exit))

/-- Deciding this terminal needs no equality test on unrelated parser labels. -/
instance terminalDecidable (l : CopyLabel) : Decidable (l = copyTerminal) := by
  unfold copyTerminal ShiTMPayloadCopyStage.payloadLabel
  cases l with
  | inl l => exact isFalse (by intro h; cases h)
  | inr l =>
    cases l with
    | inl l => exact isFalse (by intro h; cases h)
    | inr l =>
      cases l with
      | inl l => exact isFalse (by intro h; cases h)
      | inr l =>
        cases l with
        | inl l => exact isFalse (by intro h; cases h)
        | inr l =>
          cases l with
          | inl l => exact isFalse (by intro h; cases h)
          | inr l =>
            cases l with
            | none => exact isFalse (by intro h; cases h)
            | some l =>
              cases l with
              | inl l => exact isFalse (by intro h; cases h)
              | inr l => exact decidable_of_iff (l = .exit) (by simp)

abbrev Label := (Bool × CopyLabel) ⊕ ShiTMPreparedReadout.Label
def copyNumber (second : Bool) : Fin 3 := if second then 2 else 1
def copyLabel (second : Bool) (l : CopyLabel) : Label := .inl (second, l)
def readoutLabel (l : ShiTMPreparedReadout.Label) : Label := .inr l
def entry (second : Bool) : Label := copyLabel second
  (ShiTMPayloadCopyStage.cycleLabel (ShiTMReplayCycle.splitLabel false))
def afterCopy (second : Bool) : Label :=
  if second then readoutLabel (ShiTMPreparedReadout.entry 0) else entry true

def machine : Label → Stmt TopGam Label Sig
  | .inl (second, l) => if l = copyTerminal then .goto (fun _ => afterCopy second)
      else ShiTMSubroutine.stmt (copyLabel second)
        (ShiTMPayloadCopyStage.machine (copyNumber second) l)
  | .inr l => ShiTMSubroutine.stmt readoutLabel (ShiTMPreparedReadout.machine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMReplayReload.source
  k₁ := ShiTMReadout.output
  Γ := TopGam
  Λ := Label
  main := entry false
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem copy_run (second : Bool) (steps : Nat) (S U : ∀ k, List (TopGam k))
    (hr : (ShiTMPayloadCopyStage.run (copyNumber second))^[steps]
      (some ⟨some (ShiTMPayloadCopyStage.cycleLabel (ShiTMReplayCycle.splitLabel false)), none, S⟩) =
      some ⟨some copyTerminal, none, U⟩) :
    run^[steps] (some ⟨some (entry second), none, S⟩) =
      some ⟨some (copyLabel second copyTerminal), none, U⟩ := by
  exact ShiTMSubroutine.run_to_terminal (ShiTMPayloadCopyStage.machine (copyNumber second))
    machine (copyLabel second) copyTerminal rfl
    (by intro l hl; simp [machine, copyLabel, hl]) steps _ _ rfl hr

theorem copy_handoff (second : Bool) (S : ∀ k, List (TopGam k)) :
    run^[1] (some ⟨some (copyLabel second copyTerminal), none, S⟩) =
      some ⟨some (afterCopy second), none, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, copyLabel, step, stepAux]

theorem readout_run (steps : Nat) (v : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMPreparedReadout.run^[steps]
      (some ⟨some (ShiTMPreparedReadout.entry 0), none, S⟩) =
      some ⟨some (ShiTMPreparedReadout.emitLabel .finished), v, U⟩) :
    run^[steps] (some ⟨some (readoutLabel (ShiTMPreparedReadout.entry 0)), none, S⟩) =
      some ⟨some (readoutLabel (ShiTMPreparedReadout.emitLabel .finished)), v, U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMPreparedReadout.machine machine readoutLabel
    (ShiTMPreparedReadout.emitLabel .finished) rfl
    (by intro l _; rfl) steps _ _ rfl hr

end ShiTMPayloadSuffix
