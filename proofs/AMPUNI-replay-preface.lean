import «AMPUNI-output-entry-init»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayPreface

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOutputEntry

/-- A two-phase, non-destructive input copy in front of the proved entry
machine. Stack 3 is temporary scratch; retained stack 3 is the archive. The
header scanner subsequently puts the original output-index marks *above* the
archived input, so the archive does not disturb the first circuit pass. -/
abbrev ReplayLabel := Bool ⊕ StartedLabel

def copyLabel : ReplayLabel := .inl false
def restoreLabel : ReplayLabel := .inl true
def oldLabel (l : StartedLabel) : ReplayLabel := .inr l

def liftReplayStmt : Stmt TopGam StartedLabel Sig →
    Stmt TopGam ReplayLabel Sig
  | .push k f q => .push k f (liftReplayStmt q)
  | .peek k f q => .peek k f (liftReplayStmt q)
  | .pop k f q => .pop k f (liftReplayStmt q)
  | .load f q => .load f (liftReplayStmt q)
  | .branch f q₁ q₂ => .branch f (liftReplayStmt q₁) (liftReplayStmt q₂)
  | .goto f => .goto (fun v => oldLabel (f v))
  | .halt => .halt

/-- On every nonempty input cell, put one copy in scratch and one in the
archive. When the source is empty, restore scratch to source and continue at
the delimiter-seeding start label. -/
def machine : ReplayLabel → Stmt TopGam ReplayLabel Sig
  | .inl false =>
      .pop (.inl (.inl (11 : Fin 14))) pop
        (.branch isSome
          (.push (.inl (.inl (3 : Fin 14))) get
            (.push (.inr (3 : Fin 4)) get
              (.goto (fun _ => copyLabel))))
          (.goto (fun _ => restoreLabel)))
  | .inl true =>
      .pop (.inl (.inl (3 : Fin 14))) pop
        (.branch isSome
          (.push (.inl (.inl (11 : Fin 14))) get
            (.goto (fun _ => restoreLabel)))
          (.push (.inr (3 : Fin 4)) (cst .mirrorEnd)
            (.goto (fun _ => oldLabel startLabel))))
  | .inr l => liftReplayStmt (startedMachine l)

def run : Option (Cfg TopGam ReplayLabel Sig) →
    Option (Cfg TopGam ReplayLabel Sig) :=
  fun c => c.bind (step machine)

abbrev source : TopK := .inl (.inl (11 : Fin 14))
abbrev scratch : TopK := .inl (.inl (3 : Fin 14))
abbrev archive : TopK := .inr (3 : Fin 4)

/-- One source cell is copied into both the scratch and archive stacks. -/
theorem copy_cell_step (c : Cell) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hsrc : S source = c :: tail) :
    run (some { l := some copyLabel, var := v, stk := S }) =
      some ⟨some copyLabel, some c, Function.update
          (Function.update (Function.update S source tail) scratch
            (c :: S scratch)) archive (c :: S archive)⟩ := by
  simp [run, machine, copyLabel, step, stepAux, hsrc,
    pop, isSome, ShiTMLayoutMachine.get, source, scratch, archive, Function.update]

/-- Reaching the end of the source changes to the restore phase. -/
theorem copy_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hsrc : S source = []) :
    run (some { l := some copyLabel, var := v, stk := S }) =
      some ⟨some restoreLabel, none, Function.update S source []⟩ := by
  simp [run, machine, copyLabel, restoreLabel,
    step, stepAux, hsrc, pop, isSome]

/-- Restore one copied cell to the original input stack. -/
theorem restore_cell_step (c : Cell) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hscratch : S scratch = c :: tail) :
    run (some { l := some restoreLabel, var := v, stk := S }) =
      some ⟨some restoreLabel, some c,
        Function.update (Function.update S scratch tail) source
          (c :: S source)⟩ := by
  simp [run, machine, restoreLabel, step, stepAux, hscratch,
    pop, isSome, ShiTMLayoutMachine.get, source, scratch, Function.update]

/-- When scratch is empty, a sentinel separates the archive from the output
index marks that the header scanner will later place on top of it. -/
theorem restore_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hscratch : S scratch = []) :
    run (some { l := some restoreLabel, var := v, stk := S }) =
      some ⟨some (oldLabel startLabel), none,
        Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)⟩ := by
  simp [run, machine, restoreLabel, step, stepAux,
    hscratch, pop, isSome, cst, archive, scratch, Function.update]

def liftCfg (c : Cfg TopGam StartedLabel Sig) :
    Cfg TopGam ReplayLabel Sig :=
  { l := c.l.map oldLabel, var := c.var, stk := c.stk }

theorem stepAux_liftReplayStmt (q : Stmt TopGam StartedLabel Sig)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    stepAux (liftReplayStmt q) v S = liftCfg (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [liftReplayStmt, stepAux]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simp only [liftReplayStmt, stepAux]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [liftReplayStmt, stepAux]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      simp only [liftReplayStmt, stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [liftReplayStmt, stepAux]
      cases h : f v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem run_old_step (c : Option (Cfg TopGam StartedLabel Sig)) :
    run (c.map liftCfg) = (startedRun c).map liftCfg := by
  cases c with
  | none => rfl
  | some c =>
      cases c with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l =>
              change some (stepAux (liftReplayStmt (startedMachine l)) v S) =
                some (liftCfg (stepAux (startedMachine l) v S))
              rw [stepAux_liftReplayStmt]

theorem run_old (steps : Nat) (c : Option (Cfg TopGam StartedLabel Sig)) :
    run^[steps] (c.map liftCfg) = (startedRun^[steps] c).map liftCfg := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        run_old_step, ih]

/-- This machine has a genuine finite control and the same Cell-alphabet
input/output stacks as the entry machine. -/
def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := ReplayLabel
  main := copyLabel
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

end ShiTMReplayPreface
