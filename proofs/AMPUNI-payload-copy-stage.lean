import «AMPUNI-retained-payload-run»
import «AMPUNI-copy-stage-with-skip-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMPayloadCopyStage
open ShiTMLayoutMachine ShiTMRetainedTop

/-- Replay, skip retained headers, clear and rebuild local layout tables,
prepare their mirrors, and emit the circuit payload without a depth prefix. -/
abbrev Label := ShiTMReplayCycle.CycleLabel ⊕ (ShiTMReplayHeaderSkip.Phase ⊕
  (ShiTMReplayTableClear.Phase ⊕ (ShiTMPieceController.Label ⊕
    (ShiTMMirrorInit.Phase ⊕ ShiTMRetainedPayload.Label))))
def cycleLabel (l : ShiTMReplayCycle.CycleLabel) : Label := .inl l
def skipLabel (l : ShiTMReplayHeaderSkip.Phase) : Label := .inr (.inl l)
def clearLabel (l : ShiTMReplayTableClear.Phase) : Label := .inr (.inr (.inl l))
def tableLabel (l : ShiTMPieceController.Label) : Label := .inr (.inr (.inr (.inl l)))
def mirrorLabel (l : ShiTMMirrorInit.Phase) : Label := .inr (.inr (.inr (.inr (.inl l))))
def payloadLabel (l : ShiTMRetainedPayload.Label) : Label := .inr (.inr (.inr (.inr (.inr l))))

def machine (copy : Fin 3) : Label → Stmt TopGam Label Sig
  | .inl l => if l = ShiTMReplayCycle.restoreLabel true then .goto (fun _ => skipLabel 0)
      else ShiTMSubroutine.stmt cycleLabel (ShiTMReplayCycle.machine l)
  | .inr (.inl l) => if l = 4 then .goto (fun _ => clearLabel .width)
      else ShiTMSubroutine.stmt skipLabel (ShiTMReplayHeaderSkip.machine l)
  | .inr (.inr (.inl l)) => if l = .done then .goto (fun _ => tableLabel (.dispatch copy 0))
      else ShiTMSubroutine.stmt clearLabel (ShiTMReplayTableClear.machine l)
  | .inr (.inr (.inr (.inl l))) => if l = .finished copy then .goto (fun _ => mirrorLabel .startWidth)
      else ShiTMSubroutine.stmt tableLabel (ShiTMPieceController.machine l)
  | .inr (.inr (.inr (.inr (.inl l)))) => if l = .done then .goto (fun _ => payloadLabel none)
      else ShiTMSubroutine.stmt mirrorLabel (ShiTMMirrorInit.machine l)
  | .inr (.inr (.inr (.inr (.inr l)))) =>
      ShiTMSubroutine.stmt payloadLabel (ShiTMRetainedPayload.machine l)

def run (copy : Fin 3) : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run (machine copy)

def finiteMachine (copy : Fin 3) : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMReplayReload.source
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Label
  main := cycleLabel (ShiTMReplayCycle.splitLabel false)
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine copy

theorem cycle_run (copy : Fin 3) (steps : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMReplayCycle.run^[steps] (some ⟨some (ShiTMReplayCycle.splitLabel false), v, S⟩) =
      some ⟨some (ShiTMReplayCycle.restoreLabel true), v', U⟩) :
    (run copy)^[steps] (some ⟨some (cycleLabel (ShiTMReplayCycle.splitLabel false)), v, S⟩) =
      some ⟨some (cycleLabel (ShiTMReplayCycle.restoreLabel true)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMReplayCycle.machine (machine copy) cycleLabel
    (ShiTMReplayCycle.restoreLabel true) rfl
    (by intro l hl; simp [machine, cycleLabel, hl]) steps _ _ rfl hr

theorem skip_run (copy : Fin 3) (steps : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMReplayHeaderSkip.run^[steps] (some ⟨some (0), v, S⟩) =
      some ⟨some (4), v', U⟩) :
    (run copy)^[steps] (some ⟨some (skipLabel (0)), v, S⟩) =
      some ⟨some (skipLabel (4)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMReplayHeaderSkip.machine (machine copy) skipLabel
    (4) rfl
    (by intro l hl; simp [machine, skipLabel, hl]) steps _ _ rfl hr

theorem clear_run (copy : Fin 3) (steps : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMReplayTableClear.run^[steps] (some ⟨some (.width), v, S⟩) =
      some ⟨some (.done), v', U⟩) :
    (run copy)^[steps] (some ⟨some (clearLabel (.width)), v, S⟩) =
      some ⟨some (clearLabel (.done)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMReplayTableClear.machine (machine copy) clearLabel
    (.done) rfl
    (by intro l hl; simp [machine, clearLabel, hl]) steps _ _ rfl hr

theorem table_run (copy : Fin 3) (steps : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMPieceController.run^[steps] (some ⟨some (.dispatch copy 0), v, S⟩) =
      some ⟨some (.finished copy), v', U⟩) :
    (run copy)^[steps] (some ⟨some (tableLabel (.dispatch copy 0)), v, S⟩) =
      some ⟨some (tableLabel (.finished copy)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMPieceController.machine (machine copy) tableLabel
    (.finished copy) rfl
    (by intro l hl; simp [machine, tableLabel, hl]) steps _ _ rfl hr

theorem mirror_run (copy : Fin 3) (steps : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMMirrorInit.run^[steps] (some ⟨some (.startWidth), v, S⟩) =
      some ⟨some (.done), v', U⟩) :
    (run copy)^[steps] (some ⟨some (mirrorLabel (.startWidth)), v, S⟩) =
      some ⟨some (mirrorLabel (.done)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMMirrorInit.machine (machine copy) mirrorLabel
    (.done) rfl
    (by intro l hl; simp [machine, mirrorLabel, hl]) steps _ _ rfl hr

theorem payload_run (copy : Fin 3) (steps : Nat) (v v' : Sig)
    (S U : ∀ k, List (TopGam k))
    (hr : ShiTMRetainedPayload.run^[steps] (some ⟨some (none), v, S⟩) =
      some ⟨some (some (.inr .exit)), v', U⟩) :
    (run copy)^[steps] (some ⟨some (payloadLabel (none)), v, S⟩) =
      some ⟨some (payloadLabel (some (.inr .exit))), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMRetainedPayload.machine (machine copy) payloadLabel
    (some (.inr .exit)) rfl
    (by intro l hl; simp [machine, payloadLabel, hl]) steps _ _ rfl hr

theorem cycle_handoff (copy : Fin 3) (v : Sig) (S : ∀ k, List (TopGam k)) :
    (run copy)^[1] (some ⟨some (cycleLabel (ShiTMReplayCycle.restoreLabel true)), v, S⟩) =
      some ⟨some (skipLabel (0)), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, cycleLabel, step, stepAux]

theorem skip_handoff (copy : Fin 3) (v : Sig) (S : ∀ k, List (TopGam k)) :
    (run copy)^[1] (some ⟨some (skipLabel (4)), v, S⟩) =
      some ⟨some (clearLabel (.width)), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, skipLabel, step, stepAux]

theorem clear_handoff (copy : Fin 3) (v : Sig) (S : ∀ k, List (TopGam k)) :
    (run copy)^[1] (some ⟨some (clearLabel (.done)), v, S⟩) =
      some ⟨some (tableLabel (.dispatch copy 0)), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, clearLabel, step, stepAux]

theorem table_handoff (copy : Fin 3) (v : Sig) (S : ∀ k, List (TopGam k)) :
    (run copy)^[1] (some ⟨some (tableLabel (.finished copy)), v, S⟩) =
      some ⟨some (mirrorLabel (.startWidth)), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, tableLabel, step, stepAux]

theorem mirror_handoff (copy : Fin 3) (v : Sig) (S : ∀ k, List (TopGam k)) :
    (run copy)^[1] (some ⟨some (mirrorLabel (.done)), v, S⟩) =
      some ⟨some (payloadLabel (none)), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, mirrorLabel, step, stepAux]

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

/-- All six component runs compose in this single finite controller, with
exactly five extra steps for stage handoffs. -/
theorem sequence_run (copy : Fin 3) (t0 t1 t2 t3 t4 t5 : Nat)
    (v0 v1 v2 v3 v4 v5 v6 : Sig)
    (S0 S1 S2 S3 S4 S5 S6 : ∀ k, List (TopGam k))
    (h0 : ShiTMReplayCycle.run^[t0] (some ⟨some (ShiTMReplayCycle.splitLabel false), v0, S0⟩) =
      some ⟨some (ShiTMReplayCycle.restoreLabel true), v1, S1⟩)
    (h1 : ShiTMReplayHeaderSkip.run^[t1] (some ⟨some (0), v1, S1⟩) =
      some ⟨some (4), v2, S2⟩)
    (h2 : ShiTMReplayTableClear.run^[t2] (some ⟨some (.width), v2, S2⟩) =
      some ⟨some (.done), v3, S3⟩)
    (h3 : ShiTMPieceController.run^[t3] (some ⟨some (.dispatch copy 0), v3, S3⟩) =
      some ⟨some (.finished copy), v4, S4⟩)
    (h4 : ShiTMMirrorInit.run^[t4] (some ⟨some (.startWidth), v4, S4⟩) =
      some ⟨some (.done), v5, S5⟩)
    (h5 : ShiTMRetainedPayload.run^[t5] (some ⟨some (none), v5, S5⟩) =
      some ⟨some (some (.inr .exit)), v6, S6⟩)
    : (run copy)^[t0+1+t1+1+t2+1+t3+1+t4+1+t5]
        (some ⟨some (cycleLabel (ShiTMReplayCycle.splitLabel false)), v0, S0⟩) =
      some ⟨some (payloadLabel (some (.inr .exit))), v6, S6⟩ := by
  have r0 := cycle_run copy t0 v0 v1 S0 S1 h0
  have j0 := iterTwo (run copy) _ _ _ _ _ r0 (cycle_handoff copy v1 S1)
  have r1 := iterTwo (run copy) _ _ _ _ _ j0 (skip_run copy t1 v1 v2 S1 S2 h1)
  have j1 := iterTwo (run copy) _ _ _ _ _ r1 (skip_handoff copy v2 S2)
  have r2 := iterTwo (run copy) _ _ _ _ _ j1 (clear_run copy t2 v2 v3 S2 S3 h2)
  have j2 := iterTwo (run copy) _ _ _ _ _ r2 (clear_handoff copy v3 S3)
  have r3 := iterTwo (run copy) _ _ _ _ _ j2 (table_run copy t3 v3 v4 S3 S4 h3)
  have j3 := iterTwo (run copy) _ _ _ _ _ r3 (table_handoff copy v4 S4)
  have r4 := iterTwo (run copy) _ _ _ _ _ j3 (mirror_run copy t4 v4 v5 S4 S5 h4)
  have j4 := iterTwo (run copy) _ _ _ _ _ r4 (mirror_handoff copy v5 S5)
  have r5 := iterTwo (run copy) _ _ _ _ _ j4 (payload_run copy t5 v5 v6 S5 S6 h5)
  exact r5

end ShiTMPayloadCopyStage
