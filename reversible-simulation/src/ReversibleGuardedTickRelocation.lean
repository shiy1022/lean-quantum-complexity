import ReversibleFixedEmitterFrames
import ReversibleGuardedTickAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Formula agreement is independent of both the input relocation and output base. -/
theorem guardedTickCell_formula_agreement (tm : Turing.FinTM2) (capacity : Nat)
    (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm)) :
    (guardedTickCell tm k a).evaluate capacity i.val =
      ((tickFormulas (FormulaCfg.inputs tm capacity)).cells k i a).rename (naturalInputAddress tm capacity) := by
  have hg := (guardedTickFormulas_inputs_agree tm capacity i.val).2.2 k .position a
  have hx := congrArg (fun p => p.cells k i a) (naturalTickFormulas_inputs tm capacity)
  exact hg.trans hx

theorem guardedTickCell_rawCompile_relocated (tm : Turing.FinTM2) (capacity input base : Nat)
    (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm)) :
    let p := (guardedTickCell tm k a).eval (TickIndexGuard.eval capacity i.val)
    p.rawCompile (fun c => input + naturalConfigurationAddress tm capacity
      (tickSymbolicCoordinateEval capacity i.val c)) base =
      ((tickFormulas (FormulaCfg.inputs tm capacity)).cells k i a).rawCompile
        (fun j => input + j.val) base := by
  have h := congrArg (fun p => p.rawCompile (fun c => input + naturalConfigurationAddress tm capacity c) base)
    (guardedTickCell_formula_agreement tm capacity k i a)
  simpa only [DecisionTree.evaluate, Formula.rename_rawCompile, naturalInputAddress_value] using h

theorem guardedTickCell_paddedCompile_relocated (tm : Turing.FinTM2) (capacity input base bound : Nat)
    (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm)) :
    let p := (guardedTickCell tm k a).eval (TickIndexGuard.eval capacity i.val)
    p.paddedCompile (fun c => input + naturalConfigurationAddress tm capacity
      (tickSymbolicCoordinateEval capacity i.val c)) base bound =
      ((tickFormulas (FormulaCfg.inputs tm capacity)).cells k i a).paddedCompile
        (fun j => input + j.val) base bound := by
  have h := congrArg (fun p => p.paddedCompile (fun c => input + naturalConfigurationAddress tm capacity c) base bound)
    (guardedTickCell_formula_agreement tm capacity k i a)
  simpa only [DecisionTree.evaluate, Formula.rename_paddedCompile, naturalInputAddress_value] using h

end ShiReversibleGenerator
