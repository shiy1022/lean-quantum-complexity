import ReversibleTickDescendingLoopFinalBounds
import ReversibleTickSymbolRowLoopReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowDescendingTemplate_final_bounds (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (cs (.inl 2))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickSymbolRowTemplate tm stack inputStride strideBound backward).Labels (Fin 3)))) :
    let final := (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)).counters cs
    CounterBudget final (.inl 9) wireBound ∧ TickWindowBudget tm inputStride strideBound wireBound final ∧
      fixedGuardedEmitterReady (tickTraversalSupply tm) final ∧
      final (.inl 9) ≤ layers+capacity*((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) := by
  let kinds := if backward then tickSymbolRowKinds tm stack else (tickSymbolRowKinds tm stack).reverse
  have hs' : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) (cs (.inl 2))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3))) := by
    cases backward <;> simpa only [kinds,tickSymbolRowTemplate,Bool.false_eq_true,if_false,if_true,List.length_reverse] using hs
  have h := tickCoordinateListDescendingTemplate_final_bounds tm kinds inputStride strideBound backward wireBound layers capacity cs hsize hs'
  cases backward <;> simpa only [kinds,tickCoordinateListDescendingTemplate,tickSymbolRowTemplate,
    Bool.false_eq_true,if_false,if_true,List.length_reverse] using h

end ShiReversibleGenerator
