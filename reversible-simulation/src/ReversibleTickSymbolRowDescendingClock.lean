import ReversibleTickAscendingTraversalClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The concrete symbol row, in the established emission order, has a polynomial traversal clock. -/
theorem tickSymbolRowDescendingTraversal_polynomial (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
        ((tickSymbolRowTemplate tm stack inputStride strideBound backward).Labels (Fin 3))),
      TickDescendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
        ((tickSymbolRowKinds tm stack).length * (37*tickSizeBound tm+1)) count s →
      descendingSteps (programDescendingBody (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2))
        (programDescendingCost (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)) count s ≤ clock.eval n := by
  have h := tickCoordinateListDescendingTraversal_polynomial tm
    (if backward then tickSymbolRowKinds tm stack else (tickSymbolRowKinds tm stack).reverse)
    inputStride strideBound backward capacity budget layers hsize
  cases backward <;> simpa [tickSymbolRowTemplate] using h

end ShiReversibleGenerator
