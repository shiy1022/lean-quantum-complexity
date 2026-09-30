import «AMPUNI-output-header-machine»
import «AMPUNI-stage-chain-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputStage

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Output-header emission precedes table construction, which frames the
accumulator. Both controller alphabets are finite. -/
abbrev Label := ShiTMOutputHeader.Label ⊕ ShiTMStageChain.Label

def outputLabel (l : ShiTMOutputHeader.Label) : Label := .inl l
def stageLabel (l : ShiTMStageChain.Label) : Label := .inr l

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
  | .inl .finished =>
      .goto (fun _ => stageLabel (ShiTMStageChain.tailLabel (.dispatch 0 0)))
  | .inl l => liftStmt outputLabel (ShiTMOutputHeader.machine l)
  | .inr l => liftStmt stageLabel (ShiTMStageChain.machine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun cf => cf.bind (step machine)

theorem output_bridge (v : Sig) (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (outputLabel .finished), var := v, stk := S }) =
      some { l := some (stageLabel (ShiTMStageChain.tailLabel (.dispatch 0 0))), var := v, stk := S } := by
  simp [run, machine, outputLabel, stageLabel, step, stepAux]

end ShiTMOutputStage
