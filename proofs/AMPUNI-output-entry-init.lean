import «AMPUNI-output-entry-first-pass»
import «AMPUNI-output-entry-finite»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

/-- A fresh start label seeds the delimiter required by the circuit parser.
All existing entry and parser labels retain their old behavior. -/
abbrev StartedLabel := Option Label

def startLabel : StartedLabel := none
def oldLabel (l : Label) : StartedLabel := some l

def liftStartedStmt : Stmt TopGam Label Sig → Stmt TopGam StartedLabel Sig
  | .push k f q => .push k f (liftStartedStmt q)
  | .peek k f q => .peek k f (liftStartedStmt q)
  | .pop k f q => .pop k f (liftStartedStmt q)
  | .load f q => .load f (liftStartedStmt q)
  | .branch f q₁ q₂ => .branch f (liftStartedStmt q₁) (liftStartedStmt q₂)
  | .goto f => .goto (fun v => oldLabel (f v))
  | .halt => .halt

def startedMachine : StartedLabel → Stmt TopGam StartedLabel Sig
  | none =>
      .push (.inl (.inl (4 : Fin 14))) (fun _ => Cell.delim)
        (.goto (fun _ => oldLabel (headerLabel .inputLength)))
  | some l => liftStartedStmt (machine l)

def startedRun : Option (Cfg TopGam StartedLabel Sig) →
    Option (Cfg TopGam StartedLabel Sig) :=
  fun c => c.bind (step startedMachine)

def liftStartedCfg (c : Cfg TopGam Label Sig) : Cfg TopGam StartedLabel Sig :=
  { l := c.l.map oldLabel, var := c.var, stk := c.stk }

theorem stepAux_liftStartedStmt (q : Stmt TopGam Label Sig) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    stepAux (liftStartedStmt q) v S = liftStartedCfg (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [liftStartedStmt, stepAux]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simp only [liftStartedStmt, stepAux]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [liftStartedStmt, stepAux]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      simp only [liftStartedStmt, stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [liftStartedStmt, stepAux]
      cases h : f v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem started_step_old (c : Option (Cfg TopGam Label Sig)) :
    startedRun (c.map liftStartedCfg) = (run c).map liftStartedCfg := by
  cases c with
  | none => rfl
  | some c =>
      cases c with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l =>
              change some (stepAux (liftStartedStmt (machine l)) v S) =
                some (liftStartedCfg (stepAux (machine l) v S))
              rw [stepAux_liftStartedStmt]

theorem started_run_old (steps : Nat) (c : Option (Cfg TopGam Label Sig)) :
    startedRun^[steps] (c.map liftStartedCfg) =
      (run^[steps] c).map liftStartedCfg := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        started_step_old, ih]

/-- This one real machine transition establishes the first-pass delimiter invariant. -/
theorem start_step (S : ∀ k, List (TopGam k))
    (h4 : S (.inl (.inl (4 : Fin 14))) = []) :
    startedRun (some { l := some startLabel, var := none, stk := S }) =
      some (liftStartedCfg
        { l := some (headerLabel .inputLength), var := none,
          stk := Function.update S (.inl (.inl (4 : Fin 14))) [Cell.delim] }) := by
  simp [startedRun, startedMachine, startLabel, liftStartedCfg,
    step, stepAux, h4, oldLabel]

/-- The initialized finite machine has the same input and output stacks as the
entry machine, but begins with the delimiter-seeding label. -/
def startedFinMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := finite_entry_machine.1
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := StartedLabel
  main := startLabel
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := startedMachine

end ShiTMOutputEntry
