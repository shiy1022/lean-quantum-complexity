import ReversibleBindingPrinterTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

noncomputable def leafPaddedCounterTemplate (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R) :
    CounterProgramTemplate R :=
  bindingPrinterTemplate tm env (leafInputBindingTasks tm p slots) r
    (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset result) (List.ofFn slots)

theorem leafPaddedCounterTemplate_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (backward : Bool) (base : R) (offset : Nat)
    (result : SymbolicWire R) (r : NodePrinterRegisters R) (hr : r.Valid)
    (hbase : r.SourceStable base) (hslots : ∀ i, r.SourceStable (slots i))
    (hresult : r.SourceStable result.source) :
    (leafPaddedCounterTemplate tm env p slots backward base offset result r).Runs := by
  apply bindingPrinterTemplate_run tm env _ (leafInputBindingTasks_valid tm env p slots hv) r _ _ hr
  exact paddedFormulaPrinter_operations_valid backward p.intern (fun i => ⟨slots i, 0⟩)
    base offset result r hr hbase hslots hresult

theorem leafPaddedCounterTemplate_embeds (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R) :
    (leafPaddedCounterTemplate tm env p slots backward base offset result r).Embeds :=
  bindingPrinterTemplate_embeds tm env _ r _ _

theorem leafPaddedCounterTemplate_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (backward : Bool) (base : R) (offset : Nat)
    (result : SymbolicWire R) (r : NodePrinterRegisters R) (bound : Polynomial Nat) :
    (leafPaddedCounterTemplate tm env p slots backward base offset result r).PolynomiallyTimed bound :=
  bindingPrinterTemplate_polynomial tm env _ (leafInputBindingTasks_valid tm env p slots hv) r _ _ bound

theorem leafPaddedCounterTemplate_zero_slots (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (cs : R → Nat) (i : Fin p.inputList.length) :
    (leafPaddedCounterTemplate tm env p slots backward base offset result r).counters cs (slots i) = 0 :=
  leafPaddedFormulaClean_slots tm p slots _ i

end ShiReversibleGenerator
