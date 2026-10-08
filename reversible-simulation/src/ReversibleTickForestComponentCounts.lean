import ReversibleTickStackLayerCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickStackListTemplate_count (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickStackListTemplate tm stackOrder inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+(stackOrder.map (fun k => tickSymbolRowDescendingLayers tm k (cs (.inl 1)) (cs (.inl 1)))).sum := by
  induction stackOrder generalizing cs with
  | nil => simp [tickStackListTemplate,listProgramTemplate,identityProgramTemplate]
  | cons k stackOrder ih =>
    change (tickStackListTemplate tm stackOrder inputStride bound backward).counters
      ((tickStackTraversalTemplate tm k inputStride bound backward).counters cs) (.inl 9)=_
    rw [ih,tickStackTraversalTemplate_count,
      tickStackTraversalTemplate_control_frame tm k inputStride bound backward cs 1 (by decide) (by decide)]
    simp [Nat.add_assoc]

theorem tickHeaderTemplate_count (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickHeaderTemplate tm inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickCoordinateListSymbolicLayers tm (tickHeaderKinds tm) (cs (.inl 1)) 0 := by
  change (tickCoordinateListTemplate tm _ inputStride bound backward).counters (cleanupCounters [.inl 2] cs) (.inl 9)=_
  rw [tickCoordinateListTemplate_symbolic_count]
  cases backward <;> simp [cleanupCounters_apply,tickCoordinateListSymbolicLayers,List.map_reverse]

end ShiReversibleGenerator
