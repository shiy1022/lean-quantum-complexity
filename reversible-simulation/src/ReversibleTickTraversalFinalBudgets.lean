import ReversibleTickSymbolRowDescendingClock
import ReversibleConstantTraversalResult

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The descending loop ends with the same windows and the derived total layer budget. -/
theorem tickCoordinateListDescendingTraversal_final_budget (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3)))
    (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) count s) :
    TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) 0
      (descendingResult (programDescendingBody (tickCoordinateListTemplate tm kinds inputStride strideBound backward)
        (.inl 2)) count s) := by
  exact descendingResult_invariant _
    (fun k t => TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) k t)
    (fun k t ht => tickCoordinateListDescendingBudget_next tm kinds inputStride strideBound backward
      wireBound layers capacity k t hsize ht) count s hs

/-- The increasing symbol-row loop retains its windows and reaches the total layer budget. -/
theorem tickSymbolRowAscendingTraversal_final_budget (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).Labels (Fin 3)))
    (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) count s) :
    TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) 0
      (descendingResult (programDescendingBody (tickSymbolRowAscendingBody tm stack inputStride strideBound backward)
        (tickTraversalSpare tm 0)) count s) := by
  exact descendingResult_invariant _
    (fun k t => TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) k t)
    (fun k t ht => tickSymbolRowAscendingBudget_next tm stack inputStride strideBound backward
      wireBound layers capacity k t hsize ht) count s hs

end ShiReversibleGenerator
