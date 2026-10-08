import ReversibleTickStackTraversalPreservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- A complete stack leaves the same static address budget and only linearly increases the layer count. -/
theorem tickStackTraversalTemplate_final_bounds (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hl : cs (.inl 9) ≤ layers) (hsize : tickSizeBound tm ≤ strideBound) :
    let final := (tickStackTraversalTemplate tm stack inputStride strideBound backward).counters cs
    CounterBudget final (.inl 9) wireBound ∧ TickWindowBudget tm inputStride strideBound wireBound final ∧
      fixedGuardedEmitterReady (tickTraversalSupply tm) final ∧
      final (.inl 9) ≤ layers+cs (.inl 1)*((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) := by
  refine ⟨?_,tickStackTraversalTemplate_windows_preserved tm stack inputStride strideBound backward cs wireBound hw,
    tickStackTraversalTemplate_ready_preserved tm stack inputStride strideBound backward cs hr,?_⟩
  all_goals cases backward with
  | false =>
    let after := (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs
    let loop := descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound false) (.inl 2)
    have hs := tickDescendingStackSetup_invariant tm inputStride strideBound wireBound layers
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) cs
      (L := (tickSymbolRowTemplate tm stack inputStride strideBound false).Labels (Fin 3)) hr hb hw hl
    have ha : after (.inl 2)=cs (.inl 1) := by simp [after,counterCopyProgramTemplate]
    have hs' : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers (cs (.inl 1))
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (after (.inl 2))
      (⟨none,after,[]⟩ : CounterCfg _ ((tickSymbolRowTemplate tm stack inputStride strideBound false).Labels (Fin 3))) := by
      rw [ha]; exact hs
    have hf := tickSymbolRowDescendingTemplate_final_bounds tm stack inputStride strideBound false wireBound layers (cs (.inl 1)) after hsize hs'
    first
    | exact hf.1.cleanup [.inl 2,tickTraversalSpare tm 0]
    | change cleanupCounters [.inl 2,tickTraversalSpare tm 0] (loop.counters after) (.inl 9) ≤ _
      rw [cleanupCounters_apply,if_neg (by simp [tickTraversalSpare])]
      exact hf.2.2.2
  | true =>
    let cleared := (cleanupProgramTemplate [.inl 2]).counters cs
    let after := (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters cleared
    let loop := tickSymbolRowAscendingTemplate tm stack inputStride strideBound true
    have hs := tickAscendingStackSetup_invariant tm inputStride strideBound wireBound layers
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) cs
      (L := (tickSymbolRowAscendingBody tm stack inputStride strideBound true).Labels (Fin 3)) hr hb hw hl
    have ha : after (tickTraversalSpare tm 0)=cs (.inl 1) := by
      simp [after,cleared,counterCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters]
    have hs' : TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers (cs (.inl 1))
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (after (tickTraversalSpare tm 0))
      (⟨none,after,[]⟩ : CounterCfg _ ((tickSymbolRowAscendingBody tm stack inputStride strideBound true).Labels (Fin 3))) := by
      rw [ha]; exact hs
    have hf := tickSymbolRowAscendingTemplate_final_bounds tm stack inputStride strideBound true wireBound layers (cs (.inl 1)) after hsize hs'
    first
    | exact hf.1.cleanup [.inl 2,tickTraversalSpare tm 0]
    | change cleanupCounters [.inl 2,tickTraversalSpare tm 0] (loop.counters after) (.inl 9) ≤ _
      rw [cleanupCounters_apply,if_neg (by simp [tickTraversalSpare])]
      exact hf.2.2.2

end ShiReversibleGenerator
