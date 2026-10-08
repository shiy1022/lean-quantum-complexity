import ReversibleTickLoopLayerCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowDescendingLayers_ofFn (tm : Turing.FinTM2) (stack : tm.K) (capacity count : Nat) :
    tickSymbolRowDescendingLayers tm stack capacity count =
      (List.ofFn (fun i : Fin count => tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) capacity i.val)).sum := by
  induction count with
  | zero => simp [tickSymbolRowDescendingLayers]
  | succ k ih => rw [tickSymbolRowDescendingLayers,ih,List.ofFn_succ']; simp

theorem tickSymbolRowAscendingLayers_ofFn (tm : Turing.FinTM2) (stack : tm.K) (capacity position count : Nat) :
    tickSymbolRowAscendingLayers tm stack capacity position count =
      (List.ofFn (fun i : Fin count => tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) capacity (position+i.val))).sum := by
  induction count generalizing position with
  | zero => simp [tickSymbolRowAscendingLayers]
  | succ k ih =>
    rw [tickSymbolRowAscendingLayers,ih,List.ofFn_succ]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem tickSymbolRowAscendingLayers_zero (tm : Turing.FinTM2) (stack : tm.K) (capacity : Nat) :
    tickSymbolRowAscendingLayers tm stack capacity 0 capacity=tickSymbolRowDescendingLayers tm stack capacity capacity := by
  rw [tickSymbolRowAscendingLayers_ofFn,tickSymbolRowDescendingLayers_ofFn]
  simp

/-- Setup, both traversal directions and cleanup produce the same exact stack layer count. -/
theorem tickStackTraversalTemplate_count (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickStackTraversalTemplate tm stack inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickSymbolRowDescendingLayers tm stack (cs (.inl 1)) (cs (.inl 1)) := by
  cases backward with
  | false =>
    let after := (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs
    change cleanupCounters [.inl 2,tickTraversalSpare tm 0]
      ((descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride bound false) (.inl 2)).counters after) (.inl 9)=_
    rw [cleanupCounters_apply,if_neg (by simp [tickTraversalSpare]),tickSymbolRowDescendingTemplate_count]
    simp [after,counterCopyProgramTemplate]
  | true =>
    let cleared := (cleanupProgramTemplate [.inl 2]).counters cs
    let after := (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters cleared
    change cleanupCounters [.inl 2,tickTraversalSpare tm 0]
      ((tickSymbolRowAscendingTemplate tm stack inputStride bound true).counters after) (.inl 9)=_
    rw [cleanupCounters_apply,if_neg (by simp [tickTraversalSpare]),tickSymbolRowAscendingTemplate_count]
    simp [after,cleared,counterCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,tickTraversalSpare,tickSymbolRowAscendingLayers_zero]

end ShiReversibleGenerator
