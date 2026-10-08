import ReversibleTickBoundedCellPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Canonical whole-forest blocks split into the same fixed headers and runtime cells. -/
theorem tickForestPayloadBlocks_coordinates (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) :
    tickForestPayloadBlocks tm capacity input inputStride outputBase bound backward =
      tickBoundedHeaderBlocks tm capacity input inputStride outputBase bound backward ++
      tickBoundedCellBlocks tm capacity input inputStride outputBase bound backward := by
  have he : tickForestPayloadBlocks tm capacity input inputStride outputBase bound backward =
      List.ofFn (fun i : Fin (configurationWidth tm capacity) =>
        tickBoundedCoordinatePayload tm capacity input inputStride outputBase bound backward ((configurationBitEquiv tm capacity).symm i)) := by
    simp [tickForestPayloadBlocks,tickBoundedCoordinatePayload]
  rw [he,configurationBitEquiv_ofFn]
  have h := encode_flatten_blocks
    (List.ofFn (fun k : Fin (Fintype.card tm.K) => List.ofFn (fun i : Fin capacity =>
      tickBoundedSymbolBlocks tm capacity input inputStride outputBase bound backward ((Fintype.equivFin tm.K).symm k) i)))
    (fun xs : List (List Bool) => xs)
  simp [List.map_ofFn,Function.comp_def] at h
  simpa only [tickBoundedHeaderBlocks,tickBoundedCellBlocks,tickBoundedStackBlocks,tickBoundedSymbolBlocks]
    using congrArg (fun cells => tickBoundedHeaderBlocks tm capacity input inputStride outputBase bound backward ++ cells) h

/-- Symbolic traversal agrees byte-for-byte with the established padded tick forest. -/
theorem tickForestSymbolicPayload_agreement (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) (hc : 0 < capacity) :
    tickForestSymbolicPayload tm inputStride bound backward input capacity outputBase =
      ((if backward then (paddedForestCompile (fun j => input+inputStride*j.val) outputBase bound (tickForest tm capacity)).reverse
        else paddedForestCompile (fun j => input+inputStride*j.val) outputBase bound (tickForest tm capacity)).map
        (rawAssignmentPayload backward)).flatten := by
  rw [tickForest_payload_blocks,tickForestPayloadBlocks_coordinates]
  unfold tickForestSymbolicPayload
  rw [tickHeaderSymbolicPayload_bounded tm capacity input inputStride outputBase bound backward hc,
    tickCellSymbolicPayload_bounded]
  cases backward <;> simp [List.reverse_append,List.flatten_append]

/-- Exact established tick-forest bytes from the actual finite cleaned runtime program. -/
theorem tickForestTemplate_payload (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hc : 0 < cs (.inl 1)) :
    (tickForestTemplate tm inputStride bound backward).bytes cs =
      ((if backward then (paddedForestCompile (fun j => cs (.inl 0)+inputStride*j.val)
        (cs (tickTraversalSpare tm 2)) bound (tickForest tm (cs (.inl 1)))).reverse
        else paddedForestCompile (fun j => cs (.inl 0)+inputStride*j.val)
          (cs (tickTraversalSpare tm 2)) bound (tickForest tm (cs (.inl 1)))).map
        (rawAssignmentPayload backward)).flatten := by
  rw [tickForestTemplate_symbolic_payload]
  exact tickForestSymbolicPayload_agreement tm _ _ inputStride _ bound backward hc

end ShiReversibleGenerator
