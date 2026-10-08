import ReversibleResourcePrelude
import ReversibleCounterRegisterExtension
import ReversibleConditionalPrinterBounds

set_option autoImplicit false
namespace ShiReversibleGenerator

abbrev InitializationRegister := WorkspaceRegister ⊕ Fin 16

def initializationNodeRegisters : NodePrinterRegisters InitializationRegister :=
  ⟨.inr 7, .inr 8, .inr 9, .inr 10, .inl 6, .inl 5⟩

def initializationAddressCleanup : List InitializationRegister :=
  [.inr 2, .inr 3, .inr 4, .inr 5, .inr 6]

def initializationAddressOperations : List (GeneratorOperation InitializationRegister) :=
  [.affine ⟨.inl 0, .inr 2, 0, 1⟩, .affine ⟨.inr 1, .inr 2, 0, 18⟩,
    .affine ⟨.inr 2, .inr 3, 17, 1⟩, .affine ⟨.inr 0, .inr 4, 1, 1⟩]

def initializationAddressResult (cs : InitializationRegister → Nat) :=
  operationResult initializationAddressOperations (cleanupCounters initializationAddressCleanup cs)

theorem initializationAddress_valid :
    ∀ op ∈ initializationAddressOperations, op.Valid (.inl 6) (.inl 5) := by
  simp [initializationAddressOperations, GeneratorOperation.Valid, AffineAtom.Valid]

theorem initializationAddress_result (cs : InitializationRegister → Nat) :
    initializationAddressResult cs =
      Function.update (Function.update (Function.update (Function.update (Function.update cs
        (.inr 2) (cs (.inl 0) + 18 * cs (.inr 1)))
        (.inr 3) (cs (.inl 0) + 18 * cs (.inr 1) + 17))
        (.inr 4) (cs (.inr 0) + 1)) (.inr 5) 0) (.inr 6) 0 := by
  funext q
  cases q with
  | inl q =>
      simp [initializationAddressResult, initializationAddressOperations, operationResult,
        GeneratorOperation.apply, AffineAtom.apply, initializationAddressCleanup, cleanupCounters]
  | inr q =>
      fin_cases q <;> simp [initializationAddressResult, initializationAddressOperations, operationResult,
        GeneratorOperation.apply, AffineAtom.apply, initializationAddressCleanup, cleanupCounters]

abbrev InitializationAddressLabels (L : Type) :=
  CleanupLabels initializationAddressCleanup (GeneratorOperationLabels initializationAddressOperations L)

def initializationAddressCode {L : Type} (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    InitializationAddressLabels L → CounterInstr InitializationRegister (InitializationAddressLabels L) :=
  cleanupCode initializationAddressCleanup
    (operationCode initializationAddressOperations caller (.inl 6) (.inl 5) stop)
    (operationEntry initializationAddressOperations stop)

/-- Actual fixed arithmetic obtains n+18*coordinate, its padded result, and i+1. -/
theorem initializationAddress_run {L : Type} (caller : L → CounterInstr InitializationRegister L)
    (stop : L) (cs : InitializationRegister → Nat) (hb : cs (.inl 6) = 0)
    (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (initializationAddressCode caller stop)
      ⟨some (cleanupEntry initializationAddressCleanup (operationEntry initializationAddressOperations stop)), cs, ys⟩
      (cleanupSteps initializationAddressCleanup cs +
        operationSteps initializationAddressOperations (cleanupCounters initializationAddressCleanup cs))
      ⟨some (cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations stop)),
        initializationAddressResult cs, ys⟩ := by
  let inner := operationCode initializationAddressOperations caller (.inl 6) (.inl 5) stop
  let code := initializationAddressCode caller stop
  have hc := cleanupCode_run initializationAddressCleanup inner (operationEntry initializationAddressOperations stop) cs ys
  have hp := operationCode_run initializationAddressOperations caller (.inl 6) (.inl 5) stop
    initializationAddress_valid (by decide) (cleanupCounters initializationAddressCleanup cs)
    (by simpa [initializationAddressCleanup, cleanupCounters] using hb)
    (by simpa [initializationAddressCleanup, cleanupCounters] using ht) ys
  have hp' := CounterRun.relabel inner code (cleanupExit initializationAddressCleanup)
    (cleanupCode_embed initializationAddressCleanup inner (operationEntry initializationAddressOperations stop)) hp
  exact CounterRun.trans code hc hp'

theorem initializationNodeRegisters_valid : initializationNodeRegisters.Valid := by
  simp [initializationNodeRegisters, NodePrinterRegisters.Valid]

end ShiReversibleGenerator
