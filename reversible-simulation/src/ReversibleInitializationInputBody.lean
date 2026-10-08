import ReversibleInitializationAddresses
import ReversibleInitializationCellPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding

noncomputable def initializationInputYes (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) :=
  initializationYesTemplates tm e a backward (Sum.inr 0 : InitializationRegister) (.inr 2) (.inr 3)

noncomputable def initializationInputNo (tm : Turing.FinTM2) (a : Option (MachineSymbol tm)) (backward : Bool) :=
  initializationNoTemplates tm a backward (Sum.inr 0 : InitializationRegister) (.inr 2) (.inr 3)

abbrev InitializationInputCellLabels (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (L : Type) :=
  ConditionalPrinterLabels initializationNodeRegisters (initializationInputYes tm e a backward)
    (initializationInputNo tm a backward) (.inr 4) (.inl 0) (.inr 5) (.inr 6) L

noncomputable def initializationInputCellCode {L : Type} (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    InitializationInputCellLabels tm e a backward L →
      CounterInstr InitializationRegister (InitializationInputCellLabels tm e a backward L) :=
  conditionalPrinterCode initializationNodeRegisters (initializationInputYes tm e a backward)
    (initializationInputNo tm a backward) (.inr 4) (.inl 0) (.inr 5) (.inr 6) caller stop

abbrev InitializationInputBodyLabels (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (L : Type) :=
  InitializationAddressLabels (InitializationInputCellLabels tm e a backward L)

noncomputable def initializationInputBodyCode {L : Type} (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    InitializationInputBodyLabels tm e a backward L →
      CounterInstr InitializationRegister (InitializationInputBodyLabels tm e a backward L) :=
  initializationAddressCode (initializationInputCellCode tm e a backward caller stop)
    (operationEntry (comparisonCopies (.inr 4) (.inl 0) (.inr 5) (.inr 6)) (.inl 0))

noncomputable def initializationInputSelection (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) :=
  let prepared := initializationAddressResult cs
  if prepared (.inr 4) ≤ prepared (.inl 0) then initializationInputYes tm e a backward
    else initializationInputNo tm a backward

noncomputable def initializationInputBodyCounters (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) :=
  fixedNodeCounters initializationNodeRegisters (initializationInputSelection tm e a backward cs)
    (initializationAddressResult cs)

noncomputable def initializationInputBodySteps (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) : Nat :=
  let prepared := initializationAddressResult cs
  (cleanupSteps initializationAddressCleanup cs +
    operationSteps initializationAddressOperations (cleanupCounters initializationAddressCleanup cs)) +
  (operationSteps (comparisonCopies (.inr 4) (.inl 0) (.inr 5) (.inr 6)) prepared +
    comparisonSteps (prepared (.inr 4)) (prepared (.inl 0)) +
    fixedNodeSteps initializationNodeRegisters (initializationInputSelection tm e a backward cs) prepared)

/-- Fully concrete cell body: prepare addresses, run the guard, then emit the correct padded bytes. -/
theorem initializationInputBody_run {L : Type} (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (a : Option (MachineSymbol tm)) (backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = i.val)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    let copies := comparisonCopies (Sum.inr 4 : InitializationRegister) (.inl 0) (.inr 5) (.inr 6)
    let exit := operationExit copies (.inr (choicePrinterExit initializationNodeRegisters
      (initializationInputYes tm e a backward) (initializationInputNo tm a backward) stop))
    CounterRun (initializationInputBodyCode tm e a backward caller stop)
      ⟨some (cleanupEntry initializationAddressCleanup
        (operationEntry initializationAddressOperations (operationEntry copies (.inl 0)))), cs, ys⟩
      (initializationInputBodySteps tm e a backward cs)
      ⟨some (cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations exit)),
        initializationInputBodyCounters tm e a backward cs,
        initializationCellPayload tm e capacity n i a backward (n + 18 * cs (.inr 1)) ++ ys⟩ := by
  let inner := initializationInputCellCode tm e a backward caller stop
  let start : InitializationInputCellLabels tm e a backward L := operationEntry (comparisonCopies (Sum.inr 4 : InitializationRegister) (.inl 0) (.inr 5) (.inr 6)) (.inl 0)
  let code := initializationInputBodyCode tm e a backward caller stop
  let prepared := initializationAddressResult cs
  have ha := initializationAddress_run inner start cs hb ht ys
  have hp := initializationCellPrinter_run tm e capacity n i a backward
    (Sum.inr 0 : InitializationRegister) (.inr 2) (.inr 3) (.inr 4) (.inl 0) (.inr 5) (.inr 6)
    initializationNodeRegisters caller stop initializationNodeRegisters_valid
    (by simp [initializationNodeRegisters]) (by simp [initializationNodeRegisters])
    (by simp [initializationNodeRegisters])
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable])
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable])
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable])
    (by simp [comparisonCopies, GeneratorOperation.Valid, AffineAtom.Valid, initializationNodeRegisters])
    (by decide) (by decide) prepared
    (by simp [prepared, initializationAddress_result, hi])
    (by simp [prepared, initializationAddress_result, hn])
    (by simp [prepared, initializationAddress_result, hi])
    (by simp [prepared, initializationAddress_result])
    (by simp [prepared, initializationAddress_result])
    (by simp [prepared, initializationAddress_result])
    (by simpa [prepared, initializationAddress_result, initializationNodeRegisters] using hb)
    (by simpa [prepared, initializationAddress_result, initializationNodeRegisters] using ht) ys
  dsimp only at hp
  have hf : ∀ l, code (cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations l)) =
      (inner l).relabel (fun l => cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations l)) := by
    intro l
    simp only [code, initializationInputBodyCode, initializationAddressCode,
      cleanupCode_embed, operationCode_embed]
    exact CounterInstr.relabel_comp (operationExit initializationAddressOperations)
      (cleanupExit initializationAddressCleanup) (inner l)
  have hp' := CounterRun.relabel inner code
    (fun l => cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations l)) hf hp
  dsimp only [CounterCfg.relabel, Option.map] at hp'
  have h := CounterRun.trans code ha hp'
  simpa [initializationInputBodySteps, initializationInputBodyCounters, initializationInputSelection,
    initializationInputYes, initializationInputNo, prepared, initializationAddress_result, hn,
    CounterCfg.relabel, Option.map_some, code, start] using h

end ShiReversibleGenerator
