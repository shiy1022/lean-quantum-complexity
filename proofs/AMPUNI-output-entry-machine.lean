import «AMPUNI-output-stage-machine»
import «AMPUNI-retained-family-entry»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Four retained unary headers feed the numeric-output controller, then the
table initializer and nested circuit parser. -/
abbrev Label := Header ⊕ ShiTMOutputStage.Label

def headerLabel (h : Header) : Label := .inl h
def bodyLabel (l : ShiTMOutputStage.Label) : Label := .inr l

def mapTop : TopLabel → Label
  | .inr h => headerLabel h
  | .inl (.inr .circuitHeader) =>
      bodyLabel (ShiTMOutputStage.outputLabel (.dispatch 0))
  | .inl l =>
      bodyLabel (ShiTMOutputStage.stageLabel
        (ShiTMStageChain.parserLabel (.inl l)))

def liftStmt {A : Type} (f : A → Label) :
    Stmt TopGam A Sig → Stmt TopGam Label Sig
  | .push k g q => .push k g (liftStmt f q)
  | .peek k g q => .peek k g (liftStmt f q)
  | .pop k g q => .pop k g (liftStmt f q)
  | .load g q => .load g (liftStmt f q)
  | .branch g q₁ q₂ => .branch g (liftStmt f q₁) (liftStmt f q₂)
  | .goto g => .goto (fun v => f (g v))
  | .halt => .halt

def machine : Label → Stmt TopGam Label Sig
  | .inl h => liftStmt mapTop (scanRetainedHeader h)
  | .inr l => liftStmt bodyLabel (ShiTMOutputStage.machine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun cf => cf.bind (step machine)

def liftCfg {A : Type} (f : A → Label)
    (c : Cfg TopGam A Sig) : Cfg TopGam Label Sig :=
  { l := c.l.map f, var := c.var, stk := c.stk }

theorem stepAux_liftStmt {A : Type} (f : A → Label)
    (q : Stmt TopGam A Sig) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    stepAux (liftStmt f q) v S = liftCfg f (stepAux q v S) := by
  induction q generalizing v S with
  | push k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih v (Function.update S k (g v :: S k))
  | peek k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v (S k).head?) S
  | pop k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v (S k).head?) (Function.update S k (S k).tail)
  | load g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v) S
  | branch g q₁ q₂ ih₁ ih₂ =>
      simp only [liftStmt, stepAux]
      cases h : g v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto g => rfl
  | halt => rfl

theorem header_step (h : Header) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (headerLabel h), var := v, stk := S }) =
      (topRun (some { l := some (.inr h), var := v, stk := S })).map
        (liftCfg mapTop) := by
  change some (stepAux (liftStmt mapTop (scanRetainedHeader h)) v S) =
    some (liftCfg mapTop (stepAux (scanRetainedHeader h) v S))
  rw [stepAux_liftStmt]

theorem body_step (l : ShiTMOutputStage.Label) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some { l := some (bodyLabel l), var := v, stk := S }) =
      (ShiTMOutputStage.run
        (some { l := some l, var := v, stk := S })).map
          (liftCfg bodyLabel) := by
  change some (stepAux (liftStmt bodyLabel (ShiTMOutputStage.machine l)) v S) =
    some (liftCfg bodyLabel (stepAux (ShiTMOutputStage.machine l) v S))
  rw [stepAux_liftStmt]

end ShiTMOutputEntry
