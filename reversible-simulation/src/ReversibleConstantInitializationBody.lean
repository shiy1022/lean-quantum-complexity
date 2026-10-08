import ReversibleInitializationAddresses
import ReversiblePaddedFormulaPrinterRun

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula

/-- Label, memory, and non-input stack cells use one fixed constant schema. -/
def constantInitializationTemplates (value backward : Bool) :=
  paddedFormulaPrinterTemplates backward (.constant value : Formula Unit)
    (fun _ => (⟨.inr 0, 0⟩ : SymbolicWire InitializationRegister)) (.inr 2) 0 ⟨.inr 3, 0⟩

abbrev ConstantInitializationLabels (value backward : Bool) (L : Type) :=
  InitializationAddressLabels (FixedNodeLabels initializationNodeRegisters
    (constantInitializationTemplates value backward) L)

def constantInitializationEntry {L : Type} (value backward : Bool) (stop : L) :
    ConstantInitializationLabels value backward L :=
  cleanupEntry initializationAddressCleanup (operationEntry initializationAddressOperations
    (fixedNodeEntry initializationNodeRegisters (constantInitializationTemplates value backward) stop))

def constantInitializationExit {L : Type} (value backward : Bool) (stop : L) :
    ConstantInitializationLabels value backward L :=
  cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations
    (fixedNodeExit initializationNodeRegisters (constantInitializationTemplates value backward) stop))

def constantInitializationCode {L : Type} (value backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    ConstantInitializationLabels value backward L →
      CounterInstr InitializationRegister (ConstantInitializationLabels value backward L) :=
  initializationAddressCode
    (fixedNodeCode initializationNodeRegisters (constantInitializationTemplates value backward) caller stop)
    (fixedNodeEntry initializationNodeRegisters (constantInitializationTemplates value backward) stop)

def constantInitializationCounters (value backward : Bool) (cs : InitializationRegister → Nat) :=
  fixedNodeCounters initializationNodeRegisters (constantInitializationTemplates value backward)
    (initializationAddressResult cs)

def constantInitializationSteps (value backward : Bool) (cs : InitializationRegister → Nat) :=
  cleanupSteps initializationAddressCleanup cs +
    operationSteps initializationAddressOperations (cleanupCounters initializationAddressCleanup cs) +
      fixedNodeSteps initializationNodeRegisters (constantInitializationTemplates value backward)
        (initializationAddressResult cs)

def constantInitializationPayload (value backward : Bool) (base : Nat) : List Bool :=
  let nodes := (Formula.constant value : Formula Unit).paddedCompile (fun _ => 0) base 17
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

/-- Addresses are prepared by actual arithmetic, followed by actual fixed-node emission. -/
theorem constantInitialization_run {L : Type} (value backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L)
    (cs : InitializationRegister → Nat) (hb : cs (.inl 6) = 0)
    (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (constantInitializationCode value backward caller stop)
      ⟨some (constantInitializationEntry value backward stop), cs, ys⟩
      (constantInitializationSteps value backward cs)
      ⟨some (constantInitializationExit value backward stop),
        constantInitializationCounters value backward cs,
        constantInitializationPayload value backward (cs (.inl 0) + 18 * cs (.inr 1)) ++ ys⟩ := by
  let inner := fixedNodeCode initializationNodeRegisters (constantInitializationTemplates value backward) caller stop
  let entry := fixedNodeEntry initializationNodeRegisters (constantInitializationTemplates value backward) stop
  let code := constantInitializationCode value backward caller stop
  let prepared := initializationAddressResult cs
  have ha := initializationAddress_run inner entry cs hb ht ys
  have hp := paddedFormulaPrinter_run backward (.constant value : Formula Unit)
    (fun _ => (⟨.inr 0, 0⟩ : SymbolicWire InitializationRegister)) (.inr 2) 0 17 ⟨.inr 3, 0⟩
    initializationNodeRegisters caller stop initializationNodeRegisters_valid
    (by simp [initializationNodeRegisters]) (by simp [initializationNodeRegisters])
    (by simp [initializationNodeRegisters])
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable])
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable])
    (by simp [initializationNodeRegisters, NodePrinterRegisters.SourceStable]) prepared
    (by simp [prepared, SymbolicWire.eval, initializationAddress_result])
    (by simpa [prepared, initializationAddress_result, initializationNodeRegisters] using hb)
    (by simpa [prepared, initializationAddress_result, initializationNodeRegisters] using ht) ys
  dsimp only at hp
  have hbytes : paddedFormulaPrinterPayload backward (.constant value : Formula Unit)
      (fun _ => (⟨.inr 0, 0⟩ : SymbolicWire InitializationRegister)) (.inr 2) 0 17 prepared =
      constantInitializationPayload value backward (cs (.inl 0) + 18 * cs (.inr 1)) := by
    simp [paddedFormulaPrinterPayload, constantInitializationPayload, prepared,
      initializationAddress_result, Formula.paddedCompile, Formula.rawCompile]
  rw [hbytes] at hp
  have hf : ∀ l, code (cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations l)) =
      (inner l).relabel (fun l => cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations l)) := by
    intro l
    simp only [code, constantInitializationCode, initializationAddressCode,
      cleanupCode_embed, operationCode_embed]
    exact CounterInstr.relabel_comp (operationExit initializationAddressOperations)
      (cleanupExit initializationAddressCleanup) (inner l)
  have hp' := CounterRun.relabel inner code
    (fun l => cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations l)) hf hp
  dsimp only [CounterCfg.relabel, Option.map] at hp'
  have h := CounterRun.trans code ha hp'
  set_option backward.isDefEq.respectTransparency false in
    simpa only [constantInitializationSteps, constantInitializationCounters, constantInitializationEntry,
      constantInitializationExit, constantInitializationTemplates, prepared, code, inner, entry] using h

end ShiReversibleGenerator
