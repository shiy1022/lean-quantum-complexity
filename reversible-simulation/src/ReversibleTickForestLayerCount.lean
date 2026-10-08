import ReversibleTickForestComponentCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickForestLayerCount (tm : Turing.FinTM2) (capacity : Nat) : Nat :=
  tickCoordinateListSymbolicLayers tm (tickHeaderKinds tm) capacity 0+
    ((tickStackOrder tm).map (fun k => tickSymbolRowDescendingLayers tm k capacity capacity)).sum

/-- The actual full forest returns its exact layer count, independent of emission direction. -/
theorem tickForestTemplate_count (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForestTemplate tm inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickForestLayerCount tm (cs (.inl 1)) := by
  cases backward with
  | false =>
    change (tickHeaderTemplate tm inputStride bound false).counters
      ((tickStackListTemplate tm (tickStackOrder tm).reverse inputStride bound false).counters cs) (.inl 9)=_
    rw [tickHeaderTemplate_count,tickStackListTemplate_count,
      tickStackListTemplate_control_frame tm _ inputStride bound false cs 1 (by decide) (by decide)]
    simp only [tickForestLayerCount,List.map_reverse,List.sum_reverse]
    omega
  | true =>
    change (tickStackListTemplate tm (tickStackOrder tm) inputStride bound true).counters
      ((tickHeaderTemplate tm inputStride bound true).counters cs) (.inl 9)=_
    rw [tickStackListTemplate_count,tickHeaderTemplate_count,
      tickHeaderTemplate_control_frame tm inputStride bound true cs 1 (by decide) (by decide)]
    simp only [tickForestLayerCount,Nat.add_assoc]

end ShiReversibleGenerator
