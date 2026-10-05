import «AMPUNI-piece-controller-bounds»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry ShiTMPieceSchedule

def liftLabel (copy : Fin 3) (pc : PC) (atom : Atom) (table : Table) :
    EntryLabel → Label
  | .inl l => .top l
  | .inr phase => .work copy pc atom table phase

def liftCfg (copy : Fin 3) (pc : PC) (atom : Atom) (table : Table)
    (c : Cfg TopGam EntryLabel Sig) : Cfg TopGam Label Sig :=
  { l := c.l.map (liftLabel copy pc atom table), var := c.var, stk := c.stk }

/-- The controller's work statements are the previously proved copy-machine
statements with only their jump labels changed. -/
theorem stepAux_liftEntryStmt (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table)
    (q : Stmt TopGam EntryLabel Sig) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    stepAux (liftEntryStmt copy pc atom table q) v S =
      liftCfg copy pc atom table (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [liftEntryStmt, stepAux]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simp only [liftEntryStmt, stepAux]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [liftEntryStmt, stepAux]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      simp only [liftEntryStmt, stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [liftEntryStmt, stepAux]
      cases h : f v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

end ShiTMPieceController
