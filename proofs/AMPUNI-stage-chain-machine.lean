import «AMPUNI-piece-param-tail-schedule»
import «AMPUNI-piece-controller-frame-finish»
import «AMPUNI-mirror-init-parser-ready»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMStageChain

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Separate labels for the tail program, the three copy programs, mirror
initialization, and the original circuit parser. Every summand is finite. -/
abbrev Label :=
  (ShiTMPieceController.Label ⊕ ShiTMPieceController.Label) ⊕
    (ShiTMMirrorInit.Phase ⊕ TopLabel)

def tailLabel (l : ShiTMPieceController.Label) : Label := .inl (.inl l)
def copyLabel (l : ShiTMPieceController.Label) : Label := .inl (.inr l)
def mirrorLabel (p : ShiTMMirrorInit.Phase) : Label := .inr (.inl p)
def parserLabel (l : TopLabel) : Label := .inr (.inr l)

def liftStmt {A : Type} (f : A → Label) :
    Stmt TopGam A Sig → Stmt TopGam Label Sig
  | .push k g q => .push k g (liftStmt f q)
  | .peek k g q => .peek k g (liftStmt f q)
  | .pop k g q => .pop k g (liftStmt f q)
  | .load g q => .load g (liftStmt f q)
  | .branch g q₁ q₂ => .branch g (liftStmt f q₁) (liftStmt f q₂)
  | .goto g => .goto (fun v => f (g v))
  | .halt => .halt

/-- One finite TM2 control graph. The phase bridges add a single transition
after each completed program, leaving every stack unchanged. -/
def machine : Label → Stmt TopGam Label Sig
  | .inl (.inl (.finished 0)) =>
      .goto (fun _ => copyLabel (.dispatch 2 0))
  | .inl (.inl l) =>
      liftStmt tailLabel (ShiTMPieceParam.machineFor ShiTMPieceSchedule.tailProgram l)
  | .inl (.inr (.finished copy)) =>
      if copy = 2 then .goto (fun _ => copyLabel (.dispatch 1 0))
      else if copy = 1 then .goto (fun _ => copyLabel (.dispatch 0 0))
      else .goto (fun _ => mirrorLabel .startWidth)
  | .inl (.inr l) =>
      liftStmt copyLabel (ShiTMPieceController.machine l)
  | .inr (.inl .done) =>
      .goto (fun _ => parserLabel (.inl (.inr .circuitHeader)))
  | .inr (.inl p) =>
      liftStmt mirrorLabel (ShiTMMirrorInit.machine p)
  | .inr (.inr l) =>
      liftStmt parserLabel (topMachine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun cf => cf.bind (step machine)

theorem tail_bridge (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (tailLabel (.finished 0)), var := v, stk := S }) =
      some { l := some (copyLabel (.dispatch 2 0)), var := v, stk := S } := by
  simp [run, machine, tailLabel, copyLabel, step, stepAux]

theorem copy2_bridge (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (copyLabel (.finished 2)), var := v, stk := S }) =
      some { l := some (copyLabel (.dispatch 1 0)), var := v, stk := S } := by
  simp [run, machine, copyLabel, step, stepAux]

theorem copy1_bridge (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (copyLabel (.finished 1)), var := v, stk := S }) =
      some { l := some (copyLabel (.dispatch 0 0)), var := v, stk := S } := by
  simp [run, machine, copyLabel, step, stepAux]

theorem copy0_bridge (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (copyLabel (.finished 0)), var := v, stk := S }) =
      some { l := some (mirrorLabel .startWidth), var := v, stk := S } := by
  simp [run, machine, copyLabel, mirrorLabel, step, stepAux]

theorem mirror_bridge (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (mirrorLabel .done), var := v, stk := S }) =
      some { l := some (parserLabel (.inl (.inr .circuitHeader))), var := v, stk := S } := by
  simp [run, machine, mirrorLabel, parserLabel, step, stepAux]

end ShiTMStageChain
