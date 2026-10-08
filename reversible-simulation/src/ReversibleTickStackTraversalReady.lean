import ReversibleTickSymbolRowLoopReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- All runtime readiness obligations follow from the preserved generator windows and scratch-zero invariant. -/
theorem tickStackTraversalTemplate_ready (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hl : cs (.inl 9) ≤ layers) (hsize : tickSizeBound tm ≤ strideBound) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).ready cs := by
  cases backward with
  | false =>
    let after := (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs
    change cs (.inl 5)=0 ∧
      (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound false) (.inl 2)).ready after ∧ True
    refine ⟨hr.2.2.1,?_,trivial⟩
    apply tickSymbolRowDescendingTemplate_ready tm stack inputStride strideBound false wireBound layers (cs (.inl 1)) after hsize
    have h := tickDescendingStackSetup_invariant tm inputStride strideBound wireBound layers
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) cs
      (L := (tickSymbolRowTemplate tm stack inputStride strideBound false).Labels (Fin 3)) hr hb hw hl
    have hc : after (.inl 2)=cs (.inl 1) := by simp [after,counterCopyProgramTemplate]
    rw [hc]
    exact h
  | true =>
    let cleared := (cleanupProgramTemplate [.inl 2]).counters cs
    let after := (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters cleared
    change True ∧ cleared (.inl 5)=0 ∧
      (tickSymbolRowAscendingTemplate tm stack inputStride strideBound true).ready after ∧ True
    refine ⟨trivial,?_,?_,trivial⟩
    · simpa [cleared,cleanupProgramTemplate,cleanupCounters] using hr.2.2.1
    · apply tickSymbolRowAscendingTemplate_ready tm stack inputStride strideBound true wireBound layers (cs (.inl 1)) after hsize
      have h := tickAscendingStackSetup_invariant tm inputStride strideBound wireBound layers
        ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) cs
        (L := (tickSymbolRowAscendingBody tm stack inputStride strideBound true).Labels (Fin 3)) hr hb hw hl
      have hc : after (tickTraversalSpare tm 0)=cs (.inl 1) := by
        simp [after,cleared,counterCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters]
      rw [hc]
      exact h

end ShiReversibleGenerator
