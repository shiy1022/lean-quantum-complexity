import ReversibleStridedBindingPrinterTemplate
import ReversibleStridedLeafPaddedFormulaClean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

noncomputable def stridedLeafPaddedCounterTemplate (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R) :
    CounterProgramTemplate R :=
  stridedBindingPrinterTemplate tm env inputStride (leafInputBindingTasks tm p slots) r
    (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset result) (List.ofFn slots)

theorem stridedLeafPaddedCounterTemplate_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (backward : Bool) (base : R) (offset : Nat)
    (result : SymbolicWire R) (r : NodePrinterRegisters R) (hr : r.Valid)
    (hbase : r.SourceStable base) (hslots : ∀ i, r.SourceStable (slots i))
    (hresult : r.SourceStable result.source) :
    (stridedLeafPaddedCounterTemplate tm env inputStride p slots backward base offset result r).Runs := by
  apply stridedBindingPrinterTemplate_run tm env inputStride _ (leafInputBindingTasks_valid tm env p slots hv) r _ _ hr
  exact paddedFormulaPrinter_operations_valid backward p.intern (fun i => ⟨slots i, 0⟩)
    base offset result r hr hbase hslots hresult

theorem stridedLeafPaddedCounterTemplate_embeds (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R) :
    (stridedLeafPaddedCounterTemplate tm env inputStride p slots backward base offset result r).Embeds :=
  stridedBindingPrinterTemplate_embeds tm env inputStride _ r _ _

theorem stridedLeafPaddedCounterTemplate_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (backward : Bool) (base : R) (offset : Nat)
    (result : SymbolicWire R) (r : NodePrinterRegisters R) (bound : Polynomial Nat) :
    (stridedLeafPaddedCounterTemplate tm env inputStride p slots backward base offset result r).PolynomiallyTimed bound :=
  stridedBindingPrinterTemplate_polynomial tm env inputStride _ (leafInputBindingTasks_valid tm env p slots hv) r _ _ bound

theorem stridedLeafPaddedCounterTemplate_zero_slots (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (cs : R → Nat) (i : Fin p.inputList.length) :
    (stridedLeafPaddedCounterTemplate tm env inputStride p slots backward base offset result r).counters cs (slots i) = 0 :=
  leafPaddedFormulaClean_slots tm p slots _ i

end ShiReversibleGenerator
