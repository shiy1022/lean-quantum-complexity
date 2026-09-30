import «AMPUNI-payload-copy-stage»
import «AMPUNI-retained-layer-payload-run»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFirstPayload
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev Label := ShiTMReplayTableClear.Phase ⊕ (ShiTMPieceController.Label ⊕
  (ShiTMMirrorInit.Phase ⊕ ShiTMRetainedPayload.Label))
def clearLabel (l : ShiTMReplayTableClear.Phase) : Label := .inl l
def tableLabel (l : ShiTMPieceController.Label) : Label := .inr (.inl l)
def mirrorLabel (l : ShiTMMirrorInit.Phase) : Label := .inr (.inr (.inl l))
def payloadLabel (l : ShiTMRetainedPayload.Label) : Label := .inr (.inr (.inr l))

def machine : Label → Stmt TopGam Label Sig
  | .inl l => if l = .done then .goto (fun _ => tableLabel (.dispatch 0 0))
      else ShiTMSubroutine.stmt clearLabel (ShiTMReplayTableClear.machine l)
  | .inr (.inl l) => if l = .finished 0 then .goto (fun _ => mirrorLabel .startWidth)
      else ShiTMSubroutine.stmt tableLabel (ShiTMPieceController.machine l)
  | .inr (.inr (.inl l)) => if l = .done then
      .goto (fun _ => payloadLabel (some (.inr .layerDriver)))
      else ShiTMSubroutine.stmt mirrorLabel (ShiTMMirrorInit.machine l)
  | .inr (.inr (.inr l)) => ShiTMSubroutine.stmt payloadLabel (ShiTMRetainedPayload.machine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMReplayReload.source
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Label
  main := clearLabel .width
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem clear_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMReplayTableClear.run^[steps] (some ⟨some (.width), v, S⟩) =
      some ⟨some (.done), v', U⟩) :
    run^[steps] (some ⟨some (clearLabel (.width)), v, S⟩) =
      some ⟨some (clearLabel (.done)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMReplayTableClear.machine machine clearLabel
    (.done) rfl
    (by intro l hl; simp [machine, clearLabel, hl]) steps _ _ rfl hr

theorem table_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMPieceController.run^[steps] (some ⟨some (.dispatch 0 0), v, S⟩) =
      some ⟨some (.finished 0), v', U⟩) :
    run^[steps] (some ⟨some (tableLabel (.dispatch 0 0)), v, S⟩) =
      some ⟨some (tableLabel (.finished 0)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMPieceController.machine machine tableLabel
    (.finished 0) rfl
    (by intro l hl; simp [machine, tableLabel, hl]) steps _ _ rfl hr

theorem mirror_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMMirrorInit.run^[steps] (some ⟨some (.startWidth), v, S⟩) =
      some ⟨some (.done), v', U⟩) :
    run^[steps] (some ⟨some (mirrorLabel (.startWidth)), v, S⟩) =
      some ⟨some (mirrorLabel (.done)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMMirrorInit.machine machine mirrorLabel
    (.done) rfl
    (by intro l hl; simp [machine, mirrorLabel, hl]) steps _ _ rfl hr

theorem payload_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMRetainedPayload.run^[steps] (some ⟨some (some (.inr .layerDriver)), v, S⟩) =
      some ⟨some (some (.inr .exit)), v', U⟩) :
    run^[steps] (some ⟨some (payloadLabel (some (.inr .layerDriver))), v, S⟩) =
      some ⟨some (payloadLabel (some (.inr .exit))), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMRetainedPayload.machine machine payloadLabel
    (some (.inr .exit)) rfl
    (by intro l hl; simp [machine, payloadLabel, hl]) steps _ _ rfl hr

theorem clear_handoff (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some ⟨some (clearLabel (.done)), v, S⟩) =
      some ⟨some (tableLabel (.dispatch 0 0)), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, clearLabel, step, stepAux]

theorem table_handoff (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some ⟨some (tableLabel (.finished 0)), v, S⟩) =
      some ⟨some (mirrorLabel (.startWidth)), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, tableLabel, step, stepAux]

theorem mirror_handoff (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some ⟨some (mirrorLabel (.done)), v, S⟩) =
      some ⟨some (payloadLabel (some (.inr .layerDriver))), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, mirrorLabel, step, stepAux]

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

theorem sequence_run (t0 t1 t2 t3 : Nat) (v0 v1 v2 v3 v4 : Sig)
    (S0 S1 S2 S3 S4 : ∀ k, List (TopGam k))
    (h0 : ShiTMReplayTableClear.run^[t0] (some ⟨some (.width), v0, S0⟩) =
      some ⟨some (.done), v1, S1⟩)
    (h1 : ShiTMPieceController.run^[t1] (some ⟨some (.dispatch 0 0), v1, S1⟩) =
      some ⟨some (.finished 0), v2, S2⟩)
    (h2 : ShiTMMirrorInit.run^[t2] (some ⟨some (.startWidth), v2, S2⟩) =
      some ⟨some (.done), v3, S3⟩)
    (h3 : ShiTMRetainedPayload.run^[t3] (some ⟨some (some (.inr .layerDriver)), v3, S3⟩) =
      some ⟨some (some (.inr .exit)), v4, S4⟩)
    : run^[t0+1+t1+1+t2+1+t3] (some ⟨some (clearLabel .width), v0, S0⟩) =
      some ⟨some (payloadLabel (some (.inr .exit))), v4, S4⟩ := by
  have r0 := clear_run t0 v0 v1 S0 S1 h0
  have j0 := iterTwo run _ _ _ _ _ r0 (clear_handoff v1 S1)
  have r1 := iterTwo run _ _ _ _ _ j0 (table_run t1 v1 v2 S1 S2 h1)
  have j1 := iterTwo run _ _ _ _ _ r1 (table_handoff v2 S2)
  have r2 := iterTwo run _ _ _ _ _ j1 (mirror_run t2 v2 v3 S2 S3 h2)
  have j2 := iterTwo run _ _ _ _ _ r2 (mirror_handoff v3 S3)
  have r3 := iterTwo run _ _ _ _ _ j2 (payload_run t3 v3 v4 S3 S4 h3)
  exact r3

end ShiTMFirstPayload
