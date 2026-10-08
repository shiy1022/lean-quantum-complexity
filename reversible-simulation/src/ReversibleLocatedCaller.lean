import ReversibleLocatedInitializationBody

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding

theorem locatedInitializationCode_embed {L : Type} (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm)) (backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop l : L) :
    locatedInitializationCode header stackRank symbolCard symbolRank tm e a backward caller stop
      (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward l) =
    (caller l).relabel (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward) := by
  simp only [locatedInitializationCode, cellCoordinateCode, locatedInitializationExit,
    initializationInputBodyCode, initializationAddressCode, initializationBodyExit,
    cleanupCode_embed, operationCode_embed, initializationInputCellCode,
    conditionalPrinterCode, comparisonCode, choicePrinterCode, choicePrinterExit, fixedNodeCode_exit]
  cases caller l <;> rfl

end ShiReversibleGenerator
