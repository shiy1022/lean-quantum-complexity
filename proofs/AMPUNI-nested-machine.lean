import «AMPUNI-outer-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

/-- A unary count header copies its encoding to the reverse output stack while loading
one counter mark per `true` bit. A missing terminator halts instead of looping. -/
def scanHeader (counter : Fin 2) (again next : OuterControl) :
    Stmt OuterGam OuterLabel Sig :=
  Stmt.pop (.inl (11 : Fin 14)) pop
    (Stmt.branch isSome
      (Stmt.branch isMark
        (Stmt.push (.inr counter) (cst .mark)
          (Stmt.push (.inl (13 : Fin 14)) (cst .mark)
            (Stmt.goto (fun _ => .inr again))))
        (Stmt.push (.inl (13 : Fin 14)) (cst .delim)
          (Stmt.goto (fun _ => .inr next))))
      Stmt.halt)

/-- The outer counter counts layers; the inner counter counts instructions in a layer.
The instruction body is the previously verified machine, except that its terminal label
returns to the inner driver. -/
def nestedMachine : OuterLabel → Stmt OuterGam OuterLabel Sig
  | .inl l =>
      if l = b .instructionDone then Stmt.goto (fun _ => .inr .gateDriver)
      else liftStmt (loopMachine l)
  | .inr .circuitHeader => scanHeader 0 .circuitHeader .layerDriver
  | .inr .layerDriver =>
      Stmt.pop (.inr (0 : Fin 2)) pop
        (Stmt.branch isMark
          (Stmt.goto (fun _ => .inr .layerHeader))
          (Stmt.goto (fun _ => .inr .exit)))
  | .inr .layerHeader => scanHeader 1 .layerHeader .gateDriver
  | .inr .gateDriver =>
      Stmt.pop (.inr (1 : Fin 2)) pop
        (Stmt.branch isMark
          (Stmt.goto (fun _ => .inl (b .parseTag)))
          (Stmt.goto (fun _ => .inr .layerDriver)))
  | .inr .exit => Stmt.halt

def nestedRun : Option (Cfg OuterGam OuterLabel Sig) →
    Option (Cfg OuterGam OuterLabel Sig) :=
  fun cf => cf.bind (step nestedMachine)

theorem nested_instruction_done_step (v : Sig)
    (S : ∀ k, List (OuterGam k)) :
    nestedRun^[1]
      (some { l := some (.inl (b .instructionDone)), var := v, stk := S }) =
        some { l := some (.inr .gateDriver), var := v, stk := S } := by
  rfl

theorem nested_gate_driver_empty (v : Sig)
    (S : ∀ k, List (OuterGam k)) (h : S (.inr (1 : Fin 2)) = []) :
    nestedRun^[1]
      (some { l := some (.inr .gateDriver), var := v, stk := S }) =
        some { l := some (.inr .layerDriver), var := none, stk := S } := by
  simp [nestedRun, nestedMachine, step, stepAux, h, pop, isMark]

theorem nested_layer_driver_empty (v : Sig)
    (S : ∀ k, List (OuterGam k)) (h : S (.inr (0 : Fin 2)) = []) :
    nestedRun^[1]
      (some { l := some (.inr .layerDriver), var := v, stk := S }) =
        some { l := some (.inr .exit), var := none, stk := S } := by
  simp [nestedRun, nestedMachine, step, stepAux, h, pop, isMark]

end ShiTMOuterLift
