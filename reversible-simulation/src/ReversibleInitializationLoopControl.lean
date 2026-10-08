import ReversibleInitializationBodyBounds
import ReversiblePrinterContinuations
import ReversibleLoopControl

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding

noncomputable def initializationBodyExit {L : Type} (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (l : L) :
    InitializationInputBodyLabels tm e a backward L :=
  cleanupExit initializationAddressCleanup (operationExit initializationAddressOperations
    (operationExit (comparisonCopies (.inr 4) (.inl 0) (.inr 5) (.inr 6))
      (.inr (choicePrinterExit initializationNodeRegisters
        (initializationInputYes tm e a backward) (initializationInputNo tm a backward) l))))

noncomputable def initializationBodyEntry {L : Type} (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) :
    InitializationInputBodyLabels tm e a backward L :=
  cleanupEntry initializationAddressCleanup (operationEntry initializationAddressOperations
    (operationEntry (comparisonCopies (.inr 4) (.inl 0) (.inr 5) (.inr 6)) (.inl 0)))

theorem initializationBodyExit_injective {L : Type} (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) :
    Function.Injective (initializationBodyExit (L := L) tm e a backward) := by
  intro l k h
  exact choicePrinterExit_injective _ _ _ (Sum.inr.inj
    (operationExit_injective _ (operationExit_injective _ (cleanupExit_injective _ h))))

theorem initializationBodyExit_halt {L : Type} (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (stop l : L) :
    initializationInputBodyCode tm e a backward (fun _ => .halt) stop
      (initializationBodyExit tm e a backward l) = .halt := by
  simp only [initializationInputBodyCode, initializationAddressCode, initializationBodyExit,
    cleanupCode_embed, operationCode_embed, initializationInputCellCode,
    conditionalPrinterCode, comparisonCode, choicePrinterCode, choicePrinterExit,
    fixedNodeCode_exit, CounterInstr.relabel]

/-- A finite loop graph; its private body is unchanged and its public exits implement
actual test/decrement instructions on the runtime cell index. -/
noncomputable def initializationInputLoopCode (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) :
    InitializationInputBodyLabels tm e a backward (Fin 3) →
      CounterInstr InitializationRegister (InitializationInputBodyLabels tm e a backward (Fin 3)) := by
  classical
  exact reentryCode (initializationInputBodyCode tm e a backward (fun _ => .halt) 0) (.inr 0)
    (initializationBodyExit tm e a backward 0) (initializationBodyExit tm e a backward 1)
    (initializationBodyEntry tm e a backward) (initializationBodyExit tm e a backward 2)

theorem initializationInputLoop_test (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) :
    initializationInputLoopCode tm e a backward (initializationBodyExit tm e a backward 0) =
      .branch (.inr 0) (initializationBodyExit tm e a backward 2)
        (initializationBodyExit tm e a backward 1) := by
  classical
  exact reentryCode_loop _ _ _ _ _ _

theorem initializationInputLoop_pop (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) :
    initializationInputLoopCode tm e a backward (initializationBodyExit tm e a backward 1) =
      .dec (.inr 0) (initializationBodyEntry tm e a backward) := by
  classical
  apply reentryCode_pop
  intro h
  have he := initializationBodyExit_injective tm e a backward h
  exact (by decide : (1 : Fin 3) ≠ 0) he

theorem initializationInputLoop_body (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (a : Option (MachineSymbol tm)) (backward : Bool)
    (cs : InitializationRegister → Nat) (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = i.val)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (initializationInputLoopCode tm e a backward)
      ⟨some (initializationBodyEntry tm e a backward), cs, ys⟩
      (initializationInputBodySteps tm e a backward cs)
      ⟨some (initializationBodyExit tm e a backward (0 : Fin 3)),
        initializationInputBodyCounters tm e a backward cs,
        initializationCellPayload tm e capacity n i a backward (n + 18 * cs (.inr 1)) ++ ys⟩ := by
  classical
  have h := initializationInputBody_run tm e capacity n i a backward
    (fun (_ : Fin 3) => .halt) 0 cs hn hi hb ht ys
  exact reentryCode_preserves_run _ _ _ _ _ _
    (initializationBodyExit_halt tm e a backward 0 0)
    (initializationBodyExit_halt tm e a backward 0 1) h (by simp)

end ShiReversibleGenerator
