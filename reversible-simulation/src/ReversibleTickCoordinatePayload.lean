import ReversibleStridedTickCoordinateFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Exact coordinate bytes depend only on the input window, capacity, output window and position. -/
noncomputable def tickCoordinateSymbolicPayload (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (input capacity outputBase position : Nat) : List Bool :=
  let p := (tickTreeForKind tm kind).eval (TickIndexGuard.eval capacity position)
  let v := tickOutputAddressParameters tm kind bound
  let base := outputBase + v.1 + (v.2.1 * v.2.2) * capacity + v.2.2 * position
  let nodes := p.paddedCompile (fun c => input + inputStride * naturalConfigurationAddress tm capacity
    (tickSymbolicCoordinateEval capacity position c)) base bound
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

theorem stridedTickCoordinateBody_symbolic_payload (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (stridedTickCoordinateBody tm kind inputStride bound backward).bytes cs =
      tickCoordinateSymbolicPayload tm kind inputStride bound backward (cs (.inl 0)) (cs (.inl 1))
        (cs (tickTraversalSpare tm 2)) (cs (.inl 2)) := by
  let after := tickOutputPreparationCounters tm kind bound cs
  have hz : after (.inl 13) = after (.inl 12) + bound := by simp [after, tickOutputPreparationCounters]
  have h := stridedSharedFixedGuardedEmitter_payload (tickTraversalSupply tm) (tickTreeForKind tm kind)
    inputStride (tickTraversalSupply_contains tm kind) backward after bound hz
  simpa [stridedTickCoordinateBody, sequenceProgramTemplate, tickOutputPreparationTemplate,
    stridedTickTraversalEmitter, tickCoordinateSymbolicPayload, after, tickOutputPreparationCounters,
    tickPreparedOutputAddress, symbolicCellAddress, TickIndexExpr.eval] using h

theorem stridedTickCoordinateBody_bytes_source_frame (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool)
    (cs ds : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hi : cs (.inl 0) = ds (.inl 0)) (hc : cs (.inl 1) = ds (.inl 1))
    (ho : cs (tickTraversalSpare tm 2) = ds (tickTraversalSpare tm 2))
    (hp : cs (.inl 2) = ds (.inl 2)) :
    (stridedTickCoordinateBody tm kind inputStride bound backward).bytes cs =
      (stridedTickCoordinateBody tm kind inputStride bound backward).bytes ds := by
  rw [stridedTickCoordinateBody_symbolic_payload, stridedTickCoordinateBody_symbolic_payload,
    hi, hc, ho, hp]

end ShiReversibleGenerator
