import ReversibleTickSymbolRowAscendingTraversal
import ReversibleTickCoordinateListDescendingRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowTemplate_static_budget (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hi : cs (.inl 2) < cs (.inl 1)) (hs : tickSizeBound tm ≤ strideBound) :
    CounterBudget ((tickSymbolRowTemplate tm stack inputStride strideBound backward).counters cs) (.inl 9) wireBound ∧
    TickWindowBudget tm inputStride strideBound wireBound
      ((tickSymbolRowTemplate tm stack inputStride strideBound backward).counters cs) :=
  tickCoordinateListTemplate_static_budget tm _ inputStride strideBound backward cs wireBound hb hw hi hs

theorem tickSymbolRowTemplate_layer_bound (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    (tickSymbolRowTemplate tm stack inputStride strideBound backward).counters cs (.inl 9) ≤
      cs (.inl 9) + (tickSymbolRowKinds tm stack).length * (37 * tickSizeBound tm + 1) := by
  have h := tickCoordinateListTemplate_layer_bound tm
    (if backward then tickSymbolRowKinds tm stack else (tickSymbolRowKinds tm stack).reverse)
    inputStride strideBound backward cs hi
  cases backward <;> simpa [tickSymbolRowTemplate] using h

/-- Position increment retains the same address budget through the last valid cell. -/
theorem tickSymbolRowAscendingBody_static_budget (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hi : cs (.inl 2) < cs (.inl 1)) (hs : tickSizeBound tm ≤ strideBound) :
    CounterBudget ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).counters cs) (.inl 9) wireBound ∧
    TickWindowBudget tm inputStride strideBound wireBound
      ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).counters cs) := by
  have hh := tickSymbolRowTemplate_static_budget tm stack inputStride strideBound backward cs wireBound hb hw hi hs
  let after := (tickSymbolRowTemplate tm stack inputStride strideBound backward).counters cs
  have hc := hb (.inl 1) (by simp)
  have hp := tickSymbolRowTemplate_control_frame tm stack inputStride strideBound backward cs 2 (by decide)
  change CounterBudget (Function.update after (.inl 2) (after (.inl 2)+1)) (.inl 9) wireBound ∧
    TickWindowBudget tm inputStride strideBound wireBound (Function.update after (.inl 2) (after (.inl 2)+1))
  refine ⟨hh.1.update (.inl 2) _ ?_, TickWindowBudget.position_update tm inputStride strideBound wireBound after _ hh.2⟩
  dsimp only [after]
  rw [hp]
  omega

theorem tickSymbolRowAscendingBody_layer_bound (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    (tickSymbolRowAscendingBody tm stack inputStride strideBound backward).counters cs (.inl 9) ≤
      cs (.inl 9) + (tickSymbolRowKinds tm stack).length * (37 * tickSizeBound tm + 1) := by
  simpa only [tickSymbolRowAscendingBody,sequenceProgramTemplate,incrementProgramTemplate,
    Function.update_of_ne (by simp : (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 2)]
    using tickSymbolRowTemplate_layer_bound tm stack inputStride strideBound backward cs hi

end ShiReversibleGenerator
