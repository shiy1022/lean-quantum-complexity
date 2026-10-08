import ReversibleMachineTickTreeSupply

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def boundedTickFormulaForKind (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity) :
    TickTreeKind tm → Formula (Fin (configurationWidth tm capacity))
  | .inl (.inl l) => (tickFormulas (FormulaCfg.inputs tm capacity)).label l
  | .inl (.inr v) => (tickFormulas (FormulaCfg.inputs tm capacity)).memory v
  | .inr (k, a) => (tickFormulas (FormulaCfg.inputs tm capacity)).cells k i a

theorem tickTreeForKind_formula_agreement (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity)
    (kind : TickTreeKind tm) :
    (tickTreeForKind tm kind).evaluate capacity i.val =
      (boundedTickFormulaForKind tm capacity i kind).rename (naturalInputAddress tm capacity) := by
  have hg := guardedTickFormulas_inputs_agree tm capacity i.val
  have hx := naturalTickFormulas_inputs tm capacity
  cases kind with
  | inl z => cases z with
    | inl l => exact (hg.1 l).trans (congrArg (fun p => p.label l) hx)
    | inr v => exact (hg.2.1 v).trans (congrArg (fun p => p.memory v) hx)
  | inr z => exact guardedTickCell_formula_agreement tm capacity z.1 i z.2

theorem tickTreeForKind_paddedCompile_relocated (tm : Turing.FinTM2) (capacity input base bound : Nat)
    (i : Fin capacity) (kind : TickTreeKind tm) :
    let p := (tickTreeForKind tm kind).eval (TickIndexGuard.eval capacity i.val)
    p.paddedCompile (fun c => input + naturalConfigurationAddress tm capacity
      (tickSymbolicCoordinateEval capacity i.val c)) base bound =
      (boundedTickFormulaForKind tm capacity i kind).paddedCompile (fun j => input + j.val) base bound := by
  have h := congrArg (fun p => p.paddedCompile (fun c => input + naturalConfigurationAddress tm capacity c) base bound)
    (tickTreeForKind_formula_agreement tm capacity i kind)
  simpa only [DecisionTree.evaluate, Formula.rename_paddedCompile, naturalInputAddress_value] using h

end ShiReversibleGenerator
