import ReversibleInitializationFieldBound
import ReversibleLocatedConstantInitialization

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding

/-- A cell's field values depend on its addresses, never on old field contents. -/
theorem constantInitialization_fields_bound (value backward : Bool) (cs : InitializationRegister → Nat)
    (bound : Nat) (hw : cs (.inr 0) ≤ bound) (hb : cs (.inl 0) + 18 * cs (.inr 1) + 18 ≤ bound) :
    constantInitializationCounters value backward cs (.inr 7) ≤ bound ∧
    constantInitializationCounters value backward cs (.inr 8) ≤ bound ∧
    constantInitializationCounters value backward cs (.inr 9) ≤ bound := by
  simp only [constantInitializationCounters, constantInitializationTemplates]
  apply initializationSchemaPrinter_fields_bound
  · simp [Formula.size]
  · simpa [initializationAddress_result] using hw
  · simpa [initializationAddress_result] using hb
  · simp [initializationAddress_result]

theorem locatedConstant_fields_bound (header stackRank symbolCard symbolRank : Nat)
    (value : Bool)
    (backward : Bool) (cs : InitializationRegister → Nat) (bound : Nat) (hw : cs (.inr 0) ≤ bound)
    (hb : cs (.inl 0) + 18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + symbolRank) + 18 ≤ bound) :
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inr 7) ≤ bound ∧
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inr 8) ≤ bound ∧
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inr 9) ≤ bound := by
  apply constantInitialization_fields_bound
  · simpa [cellCoordinateResult_eq] using hw
  · simpa [cellCoordinateResult_eq] using hb

end ShiReversibleGenerator
