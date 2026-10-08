import ReversibleTickForestPayloadBlocks
import ReversibleStridedTickRelocation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def boundedTickCoordinate (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity) :
    TickTreeKind tm → ConfigurationBit tm capacity
  | .inl z => .inl z
  | .inr (k,a) => .inr ((k,i),a)

theorem boundedTickFormulaForKind_bitFormula (tm : Turing.FinTM2) (capacity : Nat)
    (i : Fin capacity) (kind : TickTreeKind tm) :
    boundedTickFormulaForKind tm capacity i kind =
      (tickFormulas (FormulaCfg.inputs tm capacity)).bitFormula
        (configurationBitEquiv tm capacity (boundedTickCoordinate tm capacity i kind)) := by
  unfold FormulaCfg.bitFormula
  rw [Equiv.symm_apply_apply]
  cases kind with
  | inl z => cases z <;> rfl
  | inr z => rfl

theorem tickOutputAddressParameters_coordinate (tm : Turing.FinTM2) (capacity base bound : Nat)
    (i : Fin capacity) (kind : TickTreeKind tm) :
    let v := tickOutputAddressParameters tm kind bound
    base+v.1+(v.2.1*v.2.2)*capacity+v.2.2*i.val =
      base+(configurationBitEquiv tm capacity (boundedTickCoordinate tm capacity i kind)).val*(bound+1) := by
  cases kind with
  | inl z => cases z with
    | inl l => simp [tickOutputAddressParameters,boundedTickCoordinate,configurationBitEquiv_label_val]
    | inr v => simp [tickOutputAddressParameters,boundedTickCoordinate,configurationBitEquiv_memory_val]
  | inr z =>
    simp only [tickOutputAddressParameters,boundedTickCoordinate,configurationBitEquiv_cell_val]
    ring

noncomputable def tickBoundedCoordinatePayload (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) (coordinate : ConfigurationBit tm capacity) : List Bool :=
  let rank := configurationBitEquiv tm capacity coordinate
  let nodes := ((tickFormulas (FormulaCfg.inputs tm capacity)).bitFormula rank).paddedCompile
    (fun j => input+inputStride*j.val) (outputBase+rank.val*(bound+1)) bound
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

/-- A symbolic runtime coordinate prints exactly the existing bounded tick compiler's block. -/
theorem tickCoordinateSymbolicPayload_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) (i : Fin capacity) (kind : TickTreeKind tm) :
    tickCoordinateSymbolicPayload tm kind inputStride bound backward input capacity outputBase i.val =
      tickBoundedCoordinatePayload tm capacity input inputStride outputBase bound backward
        (boundedTickCoordinate tm capacity i kind) := by
  dsimp only [tickCoordinateSymbolicPayload,tickBoundedCoordinatePayload]
  rw [tickOutputAddressParameters_coordinate]
  rw [tickTreeForKind_paddedCompile_strided,boundedTickFormulaForKind_bitFormula]

end ShiReversibleGenerator
