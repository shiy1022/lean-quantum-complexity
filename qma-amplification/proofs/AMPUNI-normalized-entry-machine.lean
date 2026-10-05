import «AMPUNI-normalized-circuit-machine»
import «AMPUNI-output-header-program-run»
import «AMPUNI-replay-init-run»
import «AMPUNI-output-entry-family»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMNormalizedEntry
open ShiTMLayoutMachine ShiTMRetainedTop

abbrev Label := Bool ⊕ (Unit ⊕ (Header ⊕
  (ShiTMOutputHeader.Label ⊕ ShiTMNormalizedCircuit.Label)))
def archiveLabel (b : Bool) : Label := .inl b
def copyLabel : Label := archiveLabel false
def restoreLabel : Label := archiveLabel true
def startLabel : Label := .inr (.inl ())
def headerLabel (h : Header) : Label := .inr (.inr (.inl h))
def outputLabel (l : ShiTMOutputHeader.Label) : Label := .inr (.inr (.inr (.inl l)))
def circuitLabel (l : ShiTMNormalizedCircuit.Label) : Label := .inr (.inr (.inr (.inr l)))
def mapTop : TopLabel → Label
  | .inr h => headerLabel h
  | .inl _ => outputLabel (.dispatch 0)
def outputEntry : Label := outputLabel (.dispatch 0)
def finished : Label := circuitLabel (ShiTMNormalizedCircuit.suffixLabel
  (ShiTMPayloadSuffix.readoutLabel (ShiTMPreparedReadout.emitLabel .finished)))
abbrev source : TopK := .inl (.inl (11 : Fin 14))
abbrev scratch : TopK := .inl (.inl (3 : Fin 14))
abbrev archive : TopK := .inr (3 : Fin 4)

def machine : Label → Stmt TopGam Label Sig
  | .inl false =>
      .pop source pop
        (.branch isSome
          (.push scratch get (.push archive get (.goto (fun _ => copyLabel))))
          (.goto (fun _ => restoreLabel)))
  | .inl true =>
      .pop scratch pop
        (.branch isSome
          (.push source get (.goto (fun _ => restoreLabel)))
          (.push archive (cst .mirrorEnd) (.goto (fun _ => startLabel))))
  | .inr (.inl _) =>
      .push (.inl (.inl (4 : Fin 14))) (cst .delim)
        (.goto (fun _ => headerLabel .inputLength))
  | .inr (.inr (.inl h)) => ShiTMSubroutine.stmt mapTop (scanRetainedHeader h)
  | .inr (.inr (.inr (.inl l))) =>
      if l = .finished then .goto (fun _ => circuitLabel (ShiTMNormalizedCircuit.prefixLabel (.inl false)))
      else ShiTMSubroutine.stmt outputLabel (ShiTMOutputHeader.machine l)
  | .inr (.inr (.inr (.inr l))) => ShiTMSubroutine.stmt circuitLabel (ShiTMNormalizedCircuit.machine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := source
  k₁ := ShiTMReadout.output
  Γ := TopGam
  Λ := Label
  main := copyLabel
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

/-- One source cell is copied into both the scratch and archive stacks. -/
theorem copy_cell_step (c : Cell) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hsrc : S source = c :: tail) :
    run (some { l := some copyLabel, var := v, stk := S }) =
      some ⟨some copyLabel, some c, Function.update
          (Function.update (Function.update S source tail) scratch
            (c :: S scratch)) archive (c :: S archive)⟩ := by
  simp [run, ShiTMSubroutine.run, machine, archiveLabel, copyLabel, step, stepAux, hsrc,
    pop, isSome, ShiTMLayoutMachine.get, source, scratch, archive, Function.update]

/-- Reaching the end of the source changes to the restore phase. -/
theorem copy_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hsrc : S source = []) :
    run (some { l := some copyLabel, var := v, stk := S }) =
      some ⟨some restoreLabel, none, Function.update S source []⟩ := by
  simp [run, ShiTMSubroutine.run, machine, archiveLabel, copyLabel, restoreLabel,
    step, stepAux, hsrc, pop, isSome]

/-- Restore one copied cell to the original input stack. -/
theorem restore_cell_step (c : Cell) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hscratch : S scratch = c :: tail) :
    run (some { l := some restoreLabel, var := v, stk := S }) =
      some ⟨some restoreLabel, some c,
        Function.update (Function.update S scratch tail) source
          (c :: S source)⟩ := by
  simp [run, ShiTMSubroutine.run, machine, archiveLabel, restoreLabel, step, stepAux, hscratch,
    pop, isSome, ShiTMLayoutMachine.get, source, scratch, Function.update]

/-- When scratch is empty, a sentinel separates the archive from the output
index marks that the header scanner will later place on top of it. -/
theorem restore_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hscratch : S scratch = []) :
    run (some { l := some restoreLabel, var := v, stk := S }) =
      some ⟨some startLabel, none,
        Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)⟩ := by
  simp [run, ShiTMSubroutine.run, machine, archiveLabel, restoreLabel, step, stepAux,
    hscratch, pop, isSome, cst, archive, scratch, Function.update]


theorem start_step (S : ∀ k, List (TopGam k))
    (h4 : S (.inl (.inl (4 : Fin 14))) = []) :
    run^[1] (some ⟨some startLabel, none, S⟩) =
      some ⟨some (headerLabel .inputLength), none,
        Function.update S (.inl (.inl (4 : Fin 14))) [Cell.delim]⟩ := by
  simp [run, ShiTMSubroutine.run, machine, startLabel, step, stepAux, h4, cst]

theorem header_step (h : Header) (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (headerLabel h), v, S⟩) =
      (topRun (some ⟨some (.inr h), v, S⟩)).map (ShiTMSubroutine.cfg mapTop) := by
  change some (stepAux (ShiTMSubroutine.stmt mapTop (scanRetainedHeader h)) v S) =
    some (ShiTMSubroutine.cfg mapTop (stepAux (scanRetainedHeader h) v S))
  rw [ShiTMSubroutine.stepAux_lift]

theorem output_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMOutputHeader.run^[steps] (some ⟨some (.dispatch 0), v, S⟩) =
      some ⟨some .finished, v', U⟩) :
    run^[steps] (some ⟨some outputEntry, v, S⟩) =
      some ⟨some (outputLabel .finished), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMOutputHeader.machine machine outputLabel
    .finished rfl (by intro l hl; simp [machine, outputLabel, hl]) steps _ _ rfl hr

theorem output_handoff (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some ⟨some (outputLabel .finished), v, S⟩) =
      some ⟨some (circuitLabel (ShiTMNormalizedCircuit.prefixLabel (.inl false))), v, S⟩ := by
  simp [run, ShiTMSubroutine.run, machine, outputLabel, step, stepAux]

theorem circuit_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMNormalizedCircuit.run^[steps]
      (some ⟨some (ShiTMNormalizedCircuit.prefixLabel (.inl false)), v, S⟩) =
        some ⟨some (ShiTMNormalizedCircuit.suffixLabel
          (ShiTMPayloadSuffix.readoutLabel (ShiTMPreparedReadout.emitLabel .finished))), v', U⟩) :
    run^[steps] (some ⟨some (circuitLabel (ShiTMNormalizedCircuit.prefixLabel (.inl false))), v, S⟩) =
      some ⟨some finished, v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMNormalizedCircuit.machine machine circuitLabel
    (ShiTMNormalizedCircuit.suffixLabel
      (ShiTMPayloadSuffix.readoutLabel (ShiTMPreparedReadout.emitLabel .finished))) rfl
    (by intro l hl; simp [machine, circuitLabel]) steps _ _ rfl hr

end ShiTMNormalizedEntry
