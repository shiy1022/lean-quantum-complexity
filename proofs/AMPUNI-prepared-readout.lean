import «AMPUNI-readout-copy-run»
import «AMPUNI-readout-scratch-run»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMPreparedReadout
open ShiTMLayoutMachine ShiTMRetainedTop
abbrev Label := (Fin 3 × ShiTMReadoutCopy.Label) ⊕ (ShiTMReadoutScratch.Label ⊕ ShiTMReadout.Label)
def copyLabel (copy : Fin 3) (l : ShiTMReadoutCopy.Label) : Label := .inl (copy, l)
def scratchLabel (l : ShiTMReadoutScratch.Label) : Label := .inr (.inl l)
def emitLabel (l : ShiTMReadout.Label) : Label := .inr (.inr l)
def entry (copy : Fin 3) : Label := copyLabel copy (ShiTMReadoutCopy.clearLabel 0)
def afterCopy (copy : Fin 3) : Label :=
  if copy = 0 then entry 1 else if copy = 1 then entry 2
  else scratchLabel (ShiTMReadoutScratch.prepLabel (.clear 0))

instance scratchTerminalDecidable (l : ShiTMReadoutScratch.Label) :
    Decidable (l = ShiTMReadoutScratch.localLabel 2) := by
  unfold ShiTMReadoutScratch.localLabel
  cases l with
  | inl l => exact isFalse (by intro h; cases h)
  | inr l =>
    cases l with
    | inl l => exact isFalse (by intro h; cases h)
    | inr k => exact decidable_of_iff (k = 2) (by simp)

def machine : Label → Stmt TopGam Label Sig
  | .inl (copy, l) => if l = ShiTMReadoutCopy.lookupLabel .finished then
      .goto (fun _ => afterCopy copy)
      else ShiTMSubroutine.stmt (copyLabel copy) (ShiTMReadoutCopy.machine copy l)
  | .inr (.inl l) => if l = ShiTMReadoutScratch.localLabel 2 then
      .goto (fun _ => emitLabel (.dispatch 0))
      else ShiTMSubroutine.stmt scratchLabel (ShiTMReadoutScratch.machine l)
  | .inr (.inr l) => ShiTMSubroutine.stmt emitLabel (ShiTMReadout.machine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ShiTMReadoutIndexLoad.archive
  k₁ := ShiTMReadout.output
  Γ := TopGam
  Λ := Label
  main := entry 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem copy_run (copy : Fin 3) (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : (ShiTMReadoutCopy.run copy)^[steps]
      (some ⟨some (ShiTMReadoutCopy.clearLabel 0), v, S⟩) =
      some ⟨some (ShiTMReadoutCopy.lookupLabel .finished), v', U⟩) :
    run^[steps] (some ⟨some (entry copy), v, S⟩) =
      some ⟨some (copyLabel copy (ShiTMReadoutCopy.lookupLabel .finished)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal (ShiTMReadoutCopy.machine copy) machine (copyLabel copy)
    (ShiTMReadoutCopy.lookupLabel .finished) rfl
    (by intro l hl; simp [machine, copyLabel, hl]) steps _ _ rfl hr

theorem scratch_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMReadoutScratch.run^[steps]
      (some ⟨some (ShiTMReadoutScratch.prepLabel (.clear 0)), v, S⟩) =
      some ⟨some (ShiTMReadoutScratch.localLabel 2), v', U⟩) :
    run^[steps] (some ⟨some (scratchLabel (ShiTMReadoutScratch.prepLabel (.clear 0))), v, S⟩) =
      some ⟨some (scratchLabel (ShiTMReadoutScratch.localLabel 2)), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMReadoutScratch.machine machine scratchLabel
    (ShiTMReadoutScratch.localLabel 2) rfl
    (by intro l hl; simp [machine, scratchLabel, hl]) steps _ _ rfl hr

theorem emit_run (steps : Nat) (v v' : Sig) (S U : ∀ k, List (TopGam k))
    (hr : ShiTMReadout.run^[steps] (some ⟨some (.dispatch 0), v, S⟩) =
      some ⟨some .finished, v', U⟩) :
    run^[steps] (some ⟨some (emitLabel (.dispatch 0)), v, S⟩) =
      some ⟨some (emitLabel .finished), v', U⟩ := by
  exact ShiTMSubroutine.run_to_terminal ShiTMReadout.machine machine emitLabel .finished rfl
    (by intro l _; rfl) steps _ _ rfl hr

private theorem retained_stable (copy : Fin 3) (h : Fin 4) :
    ShiTMReadoutCopy.Stable copy (.inr h) := by
  simp [ShiTMReadoutCopy.Stable, ShiTMReadoutCopy.core, ShiTMReadoutLookup.core,
    ShiTMReadoutCopy.destination, ShiTMReadoutLookup.destination, ShiTMReadout.wire]

private theorem retained_after (copy : Fin 3) (n w a : Nat)
    (S U : ∀ k, List (TopGam k)) (hret : ShiTMPieceController.Retained n w a S)
    (hf : ∀ k, ShiTMReadoutCopy.Stable copy k → U k = S k) :
    ShiTMPieceController.Retained n w a U :=
  ⟨(hf _ (retained_stable copy 0)).trans hret.1,
    (hf _ (retained_stable copy 1)).trans hret.2.1,
    (hf _ (retained_stable copy 2)).trans hret.2.2⟩

private theorem output_stable (copy : Fin 3) : ShiTMReadoutCopy.Stable copy ShiTMReadout.output :=
  ⟨by decide, by decide, by decide, by decide,
    Ne.symm (ShiTMReadoutCopy.destination_ne_13 copy), by decide⟩

def stageCost (n w a out : Nat) (S A B C : ∀ k, List (TopGam k)) : Nat :=
  ShiTMReadoutCopy.copyCost 0 n w a out S+1+
  ShiTMReadoutCopy.copyCost 1 n w a out A+1+
  ShiTMReadoutCopy.copyCost 2 n w a out B+1+
  ShiTMReadoutScratch.cost n w a C+1+
  (ShiTMReadout.scheduleCost (ShiTMReadout.amplifierValues n w a out) ShiTMReadout.program+1)

/-- Prepare all four operands and emit the exact majority-readout payload
in one finite controller. The input archive and accumulated earlier circuit
bytes are supplied by the preceding copy stage. No prepared-wire hypothesis
is required. This is still a typed subroutine, before Boolean finalization. -/
theorem prepared_readout_run (n w a : Nat) (out : Fin (n+(w+(a+1))))
    (tail : List Cell) (v : Sig) (S : ∀ k, List (TopGam k))
    (hret : ShiTMPieceController.Retained n w a S)
    (ha : S ShiTMReadoutIndexLoad.archive = List.replicate out.val Cell.mark ++ Cell.mirrorEnd :: tail)
    (h3 : S ShiTMReadout.scratch = []) :
    ∃ (A B C U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[stageCost n w a out.val S A B C] (some ⟨some (entry 0), v, S⟩) =
        some ⟨some (emitLabel .finished), v', U⟩
      ∧ U ShiTMReadout.output =
        ((ShiTMCircuitNormalization.stripCircPrefix (ShiClassQMAAmpX.ampReadX n w a out)).map bit).reverse ++
          S ShiTMReadout.output := by
  obtain ⟨va, A, hrA, hvA, _, h3A, hwA, hfA⟩ :=
    ShiTMReadoutCopy.prepare_readout_operand 0 n w a out tail v S hret ha h3
  obtain ⟨vb, B, hrB, hvB, _, h3B, hwB, hfB⟩ :=
    ShiTMReadoutCopy.prepare_readout_operand 1 n w a out tail va A
      (retained_after 0 n w a S A hret hfA)
      ((hfA _ (retained_stable 0 3)).trans ha) h3A
  obtain ⟨vc, C, hrC, hvC, _, h3C, hwC, hfC⟩ :=
    ShiTMReadoutCopy.prepare_readout_operand 2 n w a out tail vb B
      (retained_after 1 n w a A B (retained_after 0 n w a S A hret hfA) hfB)
      ((hfB _ (retained_stable 1 3)).trans ((hfA _ (retained_stable 0 3)).trans ha)) h3B
  have hretC := retained_after 2 n w a B C
    (retained_after 1 n w a A B (retained_after 0 n w a S A hret hfA) hfB) hfC
  obtain ⟨D, hrD, hvD, _, h3D, hfD⟩ := ShiTMReadoutScratch.prepare_run n w a vc C
    (by simpa [ShiTMFanoutPrepare.Retained, ShiTMFanoutPrepare.source, ShiTMPieceController.Retained] using hretC) h3C
  have hvalues : ∀ h, D (ShiTMReadout.wire h) =
      List.replicate (ShiTMReadout.amplifierValues n w a out.val h) Cell.mark := by
    intro h
    fin_cases h
    · exact (hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core,
        ShiTMReadout.wire])).trans
        ((hwC 0 (by decide)).trans ((hwB 0 (by decide)).trans hvA))
    · exact (hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core,
        ShiTMReadout.wire])).trans ((hwC 1 (by decide)).trans hvB)
    · exact (hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core,
        ShiTMReadout.wire])).trans hvC
    · change D (ShiTMReadoutScratch.core 7) =
        List.replicate (ShiTMReadoutScratch.value n w a) Cell.mark
      exact hvD
  obtain ⟨U, vu, hrU, hout, _⟩ := ShiTMReadout.amplifier_readout_run n w a out none D hvalues h3D
  have hDoutput : D ShiTMReadout.output = S ShiTMReadout.output := by
    rw [hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core, ShiTMReadout.wire, ShiTMReadout.output]), hfC _ (output_stable 2), hfB _ (output_stable 1), hfA _ (output_stable 0)]
  have jump (copy : Fin 3) (var : Sig) (T : ∀ k, List (TopGam k)) :
      run^[1] (some ⟨some (copyLabel copy (ShiTMReadoutCopy.lookupLabel .finished)), var, T⟩) =
        some ⟨some (afterCopy copy), var, T⟩ := by
    simp [run, ShiTMSubroutine.run, machine, copyLabel, step, stepAux]
  have jA := jump 0 va A
  have jB := jump 1 vb B
  have jC := jump 2 vc C
  have jD : run^[1] (some ⟨some (scratchLabel (ShiTMReadoutScratch.localLabel 2)), none, D⟩) =
      some ⟨some (emitLabel (.dispatch 0)), none, D⟩ := by
    simp [run, ShiTMSubroutine.run, machine, scratchLabel, step, stepAux]
  have h0 := copy_run 0 _ _ _ _ _ hrA
  have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ h0 jA
  have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 (copy_run 1 _ _ _ _ _ hrB)
  have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 jB
  have h5 := ShiTMFanout.iterTwo run _ _ _ _ _ h4 (copy_run 2 _ _ _ _ _ hrC)
  have h6 := ShiTMFanout.iterTwo run _ _ _ _ _ h5 jC
  have h7 := ShiTMFanout.iterTwo run _ _ _ _ _ h6 (scratch_run _ _ _ _ _ hrD)
  have h8 := ShiTMFanout.iterTwo run _ _ _ _ _ h7 jD
  have h9 := ShiTMFanout.iterTwo run _ _ _ _ _ h8 (emit_run _ _ _ _ _ hrU)
  refine ⟨A, B, C, U, vu, h9, ?_⟩
  rw [hout, hDoutput]

end ShiTMPreparedReadout
