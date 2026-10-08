import ReversibleSymbolicWireBounds
import ReversibleLocatedBodyBounds

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding

theorem initializationSchemaPrinter_fields_bound (p : Formula Unit) (backward : Bool)
    (cs : InitializationRegister → Nat) (bound : Nat) (hp : p.size ≤ 17)
    (hw : cs (.inr 0) ≤ bound) (hb : cs (.inr 2) + 18 ≤ bound)
    (hr : cs (.inr 3) = cs (.inr 2) + 17) :
    let ts := paddedFormulaPrinterTemplates backward p
      (fun _ => (⟨.inr 0, 0⟩ : SymbolicWire InitializationRegister)) (.inr 2) 0 ⟨.inr 3, 0⟩
    fixedNodeCounters initializationNodeRegisters ts cs (.inr 7) ≤ bound ∧
    fixedNodeCounters initializationNodeRegisters ts cs (.inr 8) ≤ bound ∧
    fixedNodeCounters initializationNodeRegisters ts cs (.inr 9) ≤ bound := by
  let inputs := fun _ : Unit => (⟨.inr 0, 0⟩ : SymbolicWire InitializationRegister)
  have hs := paddedFormulaPrinter_stable backward p inputs (.inr 2) 0 ⟨.inr 3, 0⟩ initializationNodeRegisters
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable])
    (by intro i; simp [inputs, initializationNodeRegisters, NodePrinterRegisters.SourceStable])
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable])
  have hwires := paddedFormulaPrinter_wires_bound backward p inputs (.inr 2) 0 ⟨.inr 3, 0⟩ cs bound
    (by intro i; simpa [inputs, SymbolicWire.eval] using hw)
    (by simp only [Nat.add_zero]; omega)
    (by simp only [SymbolicWire.eval, Nat.add_zero]; omega)
  exact fixedNodeCounters_fields_bound initializationNodeRegisters _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs
    (paddedFormulaPrinter_nonempty backward p inputs (.inr 2) 0 ⟨.inr 3, 0⟩) cs bound hwires

/-- A cell's field values depend on its addresses, never on old field contents. -/
theorem initializationInputBody_fields_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat)
    (bound : Nat) (hw : cs (.inr 0) ≤ bound) (hb : cs (.inl 0) + 18 * cs (.inr 1) + 18 ≤ bound) :
    initializationInputBodyCounters tm e a backward cs (.inr 7) ≤ bound ∧
    initializationInputBodyCounters tm e a backward cs (.inr 8) ≤ bound ∧
    initializationInputBodyCounters tm e a backward cs (.inr 9) ≤ bound := by
  simp only [initializationInputBodyCounters, initializationInputSelection]
  split_ifs
  · simp only [initializationInputYes, initializationYesTemplates]
    apply initializationSchemaPrinter_fields_bound
    · exact initializationInputCellSchema_size tm e a
    · simpa [initializationAddress_result] using hw
    · simpa [initializationAddress_result] using hb
    · simp [initializationAddress_result]
  · simp only [initializationInputNo, initializationNoTemplates]
    apply initializationSchemaPrinter_fields_bound
    · simp [Formula.size]
    · simpa [initializationAddress_result] using hw
    · simpa [initializationAddress_result] using hb
    · simp [initializationAddress_result]

theorem locatedInitialization_fields_bound (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) (bound : Nat) (hw : cs (.inr 0) ≤ bound)
    (hb : cs (.inl 0) + 18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + symbolRank) + 18 ≤ bound) :
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 7) ≤ bound ∧
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 8) ≤ bound ∧
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 9) ≤ bound := by
  apply initializationInputBody_fields_bound
  · simpa [cellCoordinateResult_eq] using hw
  · simpa [cellCoordinateResult_eq] using hb

end ShiReversibleGenerator
