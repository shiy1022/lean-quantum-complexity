import «AMPUNI-output-header-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry

def workLabel (pc : PC) (atom : Atom) : EntryLabel → Label
  | .inl _ => .finished
  | .inr phase => .work pc atom phase

def workCfg (pc : PC) (atom : Atom)
    (c : Cfg TopGam EntryLabel Sig) : Cfg TopGam Label Sig :=
  { l := c.l.map (workLabel pc atom), var := c.var, stk := c.stk }

theorem stepAux_liftWork (pc : PC) (atom : Atom)
    (q : Stmt TopGam EntryLabel Sig) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    stepAux (liftWork pc atom q) v S =
      workCfg pc atom (stepAux q v S) := by
  induction q generalizing v S with
  | push k g q ih =>
      simp only [liftWork, stepAux]
      exact ih v (Function.update S k (g v :: S k))
  | peek k g q ih =>
      simp only [liftWork, stepAux]
      exact ih (g v (S k).head?) S
  | pop k g q ih =>
      simp only [liftWork, stepAux]
      exact ih (g v (S k).head?) (Function.update S k (S k).tail)
  | load g q ih =>
      simp only [liftWork, stepAux]
      exact ih (g v) S
  | branch g q₁ q₂ ih₁ ih₂ =>
      simp only [liftWork, stepAux]
      cases h : g v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto g => rfl
  | halt => rfl

theorem work_step (pc : PC) (atom : Atom) (phase : Control)
    (hphase : phase ≠ .done) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (.work pc atom phase), var := v, stk := S }) =
      ((runAt (source atom) (13 : Fin 14))
        (some { l := some (.inr phase), var := v, stk := S })).map
          (workCfg pc atom) := by
  cases phase with
  | start =>
      simp [run, machine, runAt, step, workCfg, workLabel,
        stepAux_liftWork]
  | copy =>
      simp [run, machine, runAt, step, workCfg, workLabel,
        stepAux_liftWork]
  | restore =>
      simp [run, machine, runAt, step, workCfg, workLabel,
        stepAux_liftWork]
  | done => exact (hphase rfl).elim

end ShiTMOutputHeader
