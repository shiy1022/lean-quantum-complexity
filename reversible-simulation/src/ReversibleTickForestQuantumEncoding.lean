import ReversibleTickForestCountCoordinates
import ReversibleRawSubstitutionLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversible ShiReversibleGateBridge

noncomputable def tickRawNodes (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat) : List RawAssignment :=
  paddedForestCompile (fun i => input+inputStride*i.val) outputBase bound (tickForest tm capacity)

theorem tickRawNodes_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : tickSizeBound tm ≤ bound) (hout : outputBase+configurationWidth tm capacity*(bound+1) ≤ wires) :
    ∀ a ∈ tickRawNodes tm capacity input inputStride outputBase bound, a.target < wires := by
  intro a ha
  have h := (paddedForestCompile_interval (tickForest tm capacity) (fun i => input+inputStride*i.val)
    outputBase bound (fun p hp => (tickForest_size tm capacity p hp).trans hsize) a ha).2
  have ht : a.target < outputBase+configurationWidth tm capacity*(bound+1) := by
    simpa only [tickForest_length] using h
  exact ht.trans_le hout

theorem tickRawNodes_topological (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (hsize : tickSizeBound tm ≤ bound) (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase) :
    ∀ a ∈ tickRawNodes tm capacity input inputStride outputBase bound, a.Topological :=
  paddedForestCompile_topological (tickForest tm capacity) (fun i => input+inputStride*i.val) outputBase bound
    (fun p hp => (tickForest_size tm capacity p hp).trans hsize) hin

noncomputable def tickQuantumLayers (tm : Turing.FinTM2) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase)
    (hout : outputBase+configurationWidth tm capacity*(bound+1) ≤ wires) (backward : Bool) : ShiShallow.Layered wires :=
  let gates := compileAssignments (boundProgram wires (tickRawNodes tm capacity input inputStride outputBase bound)
    (tickRawNodes_bounded tm capacity input inputStride outputBase bound wires hsize hout)
    (tickRawNodes_topological tm capacity input inputStride outputBase bound hsize hin))
  substitute (if backward then gates.reverse else gates)

theorem tickQuantumLayers_payload (tm : Turing.FinTM2) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase)
    (hout : outputBase+configurationWidth tm capacity*(bound+1) ≤ wires) (backward : Bool) :
    ((if backward then (tickRawNodes tm capacity input inputStride outputBase bound).reverse
      else tickRawNodes tm capacity input inputStride outputBase bound).map (rawAssignmentPayload backward)).flatten =
      ((tickQuantumLayers tm capacity input inputStride outputBase bound wires hsize hin hout backward).map ShiBQP.encLayer).flatten :=
  rawProgramPayload_substitute _ _ (tickRawNodes_bounded tm capacity input inputStride outputBase bound wires hsize hout)
    (tickRawNodes_topological tm capacity input inputStride outputBase bound hsize hin)
    (paddedForestCompile_distinct_controls _ _ _ _) backward

theorem tickQuantumLayers_length (tm : Turing.FinTM2) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase)
    (hout : outputBase+configurationWidth tm capacity*(bound+1) ≤ wires) (backward : Bool) (hc : 0 < capacity) :
    (tickQuantumLayers tm capacity input inputStride outputBase bound wires hsize hin hout backward).length =
      tickForestLayerCount tm capacity := by
  rw [tickForestLayerCount_coordinates tm capacity hc]
  exact (rawProgram_substitute_length_both _ (tickRawNodes_bounded tm capacity input inputStride outputBase bound wires hsize hout)
    (tickRawNodes_topological tm capacity input inputStride outputBase bound hsize hin)
    (paddedForestCompile_distinct_controls _ _ _ _) backward).trans (paddedForestCompile_layerCount _ _ _ _)

end ShiReversibleGenerator
