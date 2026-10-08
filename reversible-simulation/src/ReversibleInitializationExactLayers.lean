import ReversibleInitializationLayerBound
import ReversibleConstantCellLayerBound

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

theorem formulaElementaryLayers_rename {ι κ : Type} (p : Formula ι) (f : ι → κ) :
    formulaElementaryLayers (p.rename f) = formulaElementaryLayers p := by
  induction p with
  | constant b => rfl
  | input i => rfl
  | neg p ih => simp only [Formula.rename, formulaElementaryLayers, ih]
  | conj p q ihp ihq => simp only [Formula.rename, formulaElementaryLayers, ihp, ihq]

/-- False padding emits no layers; the final copy always emits exactly one. -/
theorem constantInitialization_exact_layers (value backward : Bool)
    (cs : InitializationRegister → Nat) :
    constantInitializationCounters value backward cs (.inr 10) =
      cs (.inr 10) + formulaElementaryLayers (.constant value : Formula Unit) + 1 := by
  change fixedNodeCounters initializationNodeRegisters (constantInitializationTemplates value backward)
    (initializationAddressResult cs) initializationNodeRegisters.count = _
  rw [fixedNodeCounters_count _ _ (by decide) (by decide) (by decide)]
  simp [constantInitializationTemplates, paddedFormulaPrinter_layer_count,
    initializationNodeRegisters, initializationAddress_result, Nat.add_assoc]

/-- The runtime comparison chooses the exact input or padding layer count. -/
theorem initializationInputBody_exact_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) :
    initializationInputBodyCounters tm e a backward cs (.inr 10) = cs (.inr 10) +
      (if cs (.inr 0) < cs (.inl 0) then formulaElementaryLayers (initializationInputCellSchema tm e a)
       else formulaElementaryLayers (.constant (oneHot none a) : Formula Unit)) + 1 := by
  classical
  change fixedNodeCounters initializationNodeRegisters (initializationInputSelection tm e a backward cs)
    (initializationAddressResult cs) initializationNodeRegisters.count = _
  rw [fixedNodeCounters_count _ _ (by decide) (by decide) (by decide)]
  have hcmp : cs (.inr 0) + 1 ≤ cs (.inl 0) ↔ cs (.inr 0) < cs (.inl 0) := by omega
  simp only [initializationInputSelection, initializationAddress_result] at *
  simp only [Function.update_apply] at *
  by_cases h : cs (.inr 0) < cs (.inl 0) <;>
    simp [initializationInputYes, initializationInputNo, initializationYesTemplates,
    initializationNoTemplates, paddedFormulaPrinter_layer_count,
    initializationNodeRegisters, hcmp, h, Nat.add_assoc]

theorem locatedConstant_exact_layers (header stackRank symbolCard symbolRank : Nat)
    (value backward : Bool) (cs : InitializationRegister → Nat) :
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inr 10) =
      cs (.inr 10) + formulaElementaryLayers (.constant value : Formula Unit) + 1 := by
  simpa [locatedConstantCounters, cellCoordinateResult_eq] using
    constantInitialization_exact_layers value backward
      (cellCoordinateResult header stackRank symbolCard symbolRank cs)

theorem locatedInitialization_exact_layers (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) :
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 10) =
      cs (.inr 10) +
        (if cs (.inr 0) < cs (.inl 0) then formulaElementaryLayers (initializationInputCellSchema tm e a)
         else formulaElementaryLayers (.constant (oneHot none a) : Formula Unit)) + 1 := by
  simpa [locatedInitializationCounters, cellCoordinateResult_eq] using
    initializationInputBody_exact_layers tm e a backward
      (cellCoordinateResult header stackRank symbolCard symbolRank cs)

end ShiReversibleGenerator
