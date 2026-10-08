import ReversibleMachineTickRelocation
import ReversibleStridedTickCoordinateBindingClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickTreeForKind_paddedCompile_strided (tm : Turing.FinTM2) (capacity input inputStride base bound : Nat)
    (i : Fin capacity) (kind : TickTreeKind tm) :
    let p := (tickTreeForKind tm kind).eval (TickIndexGuard.eval capacity i.val)
    p.paddedCompile (fun c => input + inputStride * naturalConfigurationAddress tm capacity
      (tickSymbolicCoordinateEval capacity i.val c)) base bound =
      (boundedTickFormulaForKind tm capacity i kind).paddedCompile (fun j => input + inputStride * j.val) base bound := by
  have h := congrArg (fun p => p.paddedCompile (fun c => input + inputStride * naturalConfigurationAddress tm capacity c) base bound)
    (tickTreeForKind_formula_agreement tm capacity i kind)
  simpa only [DecisionTree.evaluate, Formula.rename_paddedCompile, naturalInputAddress_value] using h

theorem stridedTickCoordinateAddress_input (tm : Turing.FinTM2) {R : Type} [DecidableEq R]
    (r : CoordinateBindingRegisters R) (inputStride : Nat) (cs : R → Nat)
    (j : Fin (configurationWidth tm (cs r.capacity))) (coordinate : TickSymbolicCoordinate tm)
    (hc : tickSymbolicCoordinateEval (cs r.capacity) (cs r.position) coordinate =
      naturalInputAddress tm (cs r.capacity) j) :
    stridedTickCoordinateAddress tm r inputStride coordinate cs = cs r.input + inputStride * j.val := by
  simp only [stridedTickCoordinateAddress, hc, naturalInputAddress_value]

end ShiReversibleGenerator
