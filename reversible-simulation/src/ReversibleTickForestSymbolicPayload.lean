import ReversibleTickForestInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickHeaderSymbolicPayload (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (input capacity outputBase : Nat) : List Bool :=
  ((if backward then (tickHeaderKinds tm).reverse else tickHeaderKinds tm).map (fun kind =>
    tickCoordinateSymbolicPayload tm kind inputStride bound backward input capacity outputBase 0)).flatten

noncomputable def tickCellSymbolicPayload (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (input capacity outputBase : Nat) : List Bool :=
  ((if backward then (tickStackOrder tm).reverse else tickStackOrder tm).map (fun k =>
    if backward then tickSymbolRowAscendingBytes tm k inputStride bound backward input capacity outputBase 0 capacity
    else tickSymbolRowDescendingBytes tm k inputStride bound backward input capacity outputBase capacity)).flatten

noncomputable def tickForestSymbolicPayload (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (input capacity outputBase : Nat) : List Bool :=
  let header := tickHeaderSymbolicPayload tm inputStride bound backward input capacity outputBase
  let cells := tickCellSymbolicPayload tm inputStride bound backward input capacity outputBase
  if backward then cells++header else header++cells

theorem tickHeaderTemplate_payload (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickHeaderTemplate tm inputStride bound backward).bytes cs =
      tickHeaderSymbolicPayload tm inputStride bound backward (cs (.inl 0)) (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) := by
  change (tickCoordinateListTemplate tm _ inputStride bound backward).bytes (cleanupCounters [.inl 2] cs) ++ [] = _
  rw [tickCoordinateListTemplate_payload]
  cases backward <;> simp [tickHeaderSymbolicPayload,cleanupCounters_apply,tickTraversalSpare]

/-- Exact bytes of the complete runtime program, including every setup and cleanup operation. -/
theorem tickForestTemplate_symbolic_payload (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForestTemplate tm inputStride bound backward).bytes cs =
      tickForestSymbolicPayload tm inputStride bound backward (cs (.inl 0)) (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) := by
  cases backward with
  | false =>
    let after := (tickStackListTemplate tm (tickStackOrder tm).reverse inputStride bound false).counters cs
    change (tickHeaderTemplate tm inputStride bound false).bytes after ++
      (tickStackListTemplate tm (tickStackOrder tm).reverse inputStride bound false).bytes cs = _
    rw [tickHeaderTemplate_payload,tickStackListTemplate_payload]
    have h0 : after (.inl 0)=cs (.inl 0) := tickStackListTemplate_control_frame tm _ inputStride bound false cs 0 (by decide) (by decide)
    have h1 : after (.inl 1)=cs (.inl 1) := tickStackListTemplate_control_frame tm _ inputStride bound false cs 1 (by decide) (by decide)
    have h2 : after (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2) := tickStackListTemplate_spare_frame tm _ inputStride bound false cs 2 (by decide)
    simp only [h0,h1,h2,tickForestSymbolicPayload,tickCellSymbolicPayload,Bool.false_eq_true,if_false,List.reverse_reverse]
  | true =>
    let after := (tickHeaderTemplate tm inputStride bound true).counters cs
    change (tickStackListTemplate tm (tickStackOrder tm) inputStride bound true).bytes after ++
      (tickHeaderTemplate tm inputStride bound true).bytes cs = _
    rw [tickStackListTemplate_payload,tickHeaderTemplate_payload]
    have h0 : after (.inl 0)=cs (.inl 0) := tickHeaderTemplate_control_frame tm inputStride bound true cs 0 (by decide) (by decide)
    have h1 : after (.inl 1)=cs (.inl 1) := tickHeaderTemplate_control_frame tm inputStride bound true cs 1 (by decide) (by decide)
    have h2 : after (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2) := tickHeaderTemplate_spare_frame tm inputStride bound true cs 2
    simp only [h0,h1,h2,tickForestSymbolicPayload,tickCellSymbolicPayload,if_true]

end ShiReversibleGenerator
