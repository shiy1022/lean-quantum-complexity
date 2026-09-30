import «AMPUNI-global-fanout-prefix»
import «AMPUNI-first-payload-machine»
import «AMPUNI-payload-suffix-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMNormalizedCircuit
open ShiTMLayoutMachine ShiTMRetainedTop

def prefixTerminal : ShiTMGlobalFanoutPrefix.Label := .inr ShiTMFanoutStage.finished
def firstTerminal : ShiTMFirstPayload.Label := ShiTMFirstPayload.payloadLabel (some (.inr .exit))
instance firstTerminalDecidable (l : ShiTMFirstPayload.Label) : Decidable (l = firstTerminal) := by
  unfold firstTerminal ShiTMFirstPayload.payloadLabel
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

abbrev Label := ShiTMGlobalFanoutPrefix.Label ⊕ (ShiTMFirstPayload.Label ⊕ ShiTMPayloadSuffix.Label)
def prefixLabel (l : ShiTMGlobalFanoutPrefix.Label) : Label := .inl l
def firstLabel (l : ShiTMFirstPayload.Label) : Label := .inr (.inl l)
def suffixLabel (l : ShiTMPayloadSuffix.Label) : Label := .inr (.inr l)

def machine : Label → Stmt TopGam Label Sig
  | .inl l => if l = prefixTerminal then .goto (fun _ => firstLabel (ShiTMFirstPayload.clearLabel .width))
      else ShiTMSubroutine.stmt prefixLabel (ShiTMGlobalFanoutPrefix.machine l)
  | .inr (.inl l) => if l = firstTerminal then .goto (fun _ => suffixLabel (ShiTMPayloadSuffix.entry false))
      else ShiTMSubroutine.stmt firstLabel (ShiTMFirstPayload.machine l)
  | .inr (.inr l) => ShiTMSubroutine.stmt suffixLabel (ShiTMPayloadSuffix.machine l)

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
  main := prefixLabel (.inl false)
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem prefix_run (steps : Nat) (v : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMGlobalFanoutPrefix.run^[steps] (some ⟨some (.inl false), v, S⟩) =
      some ⟨some (prefixTerminal), none, U⟩) :
    run^[steps] (some ⟨some (prefixLabel (.inl false)), v, S⟩) =
      some ⟨some (prefixLabel (prefixTerminal)), none, U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMGlobalFanoutPrefix.machine machine prefixLabel
    (prefixTerminal) rfl
    (by intro l hl; simp [machine, prefixLabel, hl]) steps _ _ rfl hr

theorem first_run (steps : Nat) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMFirstPayload.run^[steps] (some ⟨some (ShiTMFirstPayload.clearLabel .width), none, S⟩) =
      some ⟨some (firstTerminal), none, U⟩) :
    run^[steps] (some ⟨some (firstLabel (ShiTMFirstPayload.clearLabel .width)), none, S⟩) =
      some ⟨some (firstLabel (firstTerminal)), none, U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMFirstPayload.machine machine firstLabel
    (firstTerminal) rfl
    (by intro l hl; simp [machine, firstLabel, hl]) steps _ _ rfl hr

theorem suffix_run (steps : Nat) (v : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMPayloadSuffix.run^[steps] (some ⟨some (ShiTMPayloadSuffix.entry false), none, S⟩) =
      some ⟨some (ShiTMPayloadSuffix.readoutLabel (ShiTMPreparedReadout.emitLabel .finished)), v, U⟩) :
    run^[steps] (some ⟨some (suffixLabel (ShiTMPayloadSuffix.entry false)), none, S⟩) =
      some ⟨some (suffixLabel (ShiTMPayloadSuffix.readoutLabel (ShiTMPreparedReadout.emitLabel .finished))), v, U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMPayloadSuffix.machine machine suffixLabel
    (ShiTMPayloadSuffix.readoutLabel (ShiTMPreparedReadout.emitLabel .finished)) rfl
    (by intro l hl; simp [machine, suffixLabel, hl]) steps _ _ rfl hr

theorem prefix_handoff (S : ∀ k, List (TopGam k)) :
    run^[1] (some ⟨some (prefixLabel prefixTerminal), none, S⟩) =
      some ⟨some (firstLabel (ShiTMFirstPayload.clearLabel .width)), none, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, prefixLabel, step, stepAux]

theorem first_handoff (S : ∀ k, List (TopGam k)) :
    run^[1] (some ⟨some (firstLabel firstTerminal), none, S⟩) =
      some ⟨some (suffixLabel (ShiTMPayloadSuffix.entry false)), none, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, firstLabel, step, stepAux]

end ShiTMNormalizedCircuit
