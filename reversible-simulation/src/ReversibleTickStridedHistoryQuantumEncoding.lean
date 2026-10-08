import ReversibleTickInverseHistoryPayload
import ReversiblePaddedIterationElementaryLayers
import ReversibleRawSubstitutionLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversible ShiReversibleGateBridge

/-- Only the first history slice uses the supplied input stride; later slices use padded results. -/
noncomputable def tickStridedHistoryRawNodes (tm : Turing.FinTM2) (capacity input inputStride outputBase bound t : Nat) : List RawAssignment :=
  paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound t
    (fun i => input+inputStride*i.val) outputBase

theorem tickStridedHistoryRawNodes_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) :
    ∀ a ∈ tickStridedHistoryRawNodes tm capacity input inputStride outputBase bound t,a.target < wires := by
  intro a ha
  exact ((paddedIterationCompile_interval (tickForest tm capacity) (tickForest_length tm capacity) bound
    (fun p hp => (tickForest_size tm capacity p hp).trans hsize) t _ outputBase a ha).2).trans_le hout

theorem tickStridedHistoryRawNodes_topological (tm : Turing.FinTM2) (capacity input inputStride outputBase bound t : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+inputStride*i.val < outputBase) :
    ∀ a ∈ tickStridedHistoryRawNodes tm capacity input inputStride outputBase bound t,a.Topological :=
  paddedIterationCompile_topological (tickForest tm capacity) (tickForest_length tm capacity) bound
    (fun p hp => (tickForest_size tm capacity p hp).trans hsize) t _ outputBase hin

noncomputable def tickStridedHistoryQuantumLayers (tm : Turing.FinTM2) (capacity input inputStride outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+inputStride*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) (backward : Bool) : ShiShallow.Layered wires :=
  let gates := compileAssignments (boundProgram wires (tickStridedHistoryRawNodes tm capacity input inputStride outputBase bound t)
    (tickStridedHistoryRawNodes_bounded tm capacity input inputStride outputBase bound t wires hsize hout)
    (tickStridedHistoryRawNodes_topological tm capacity input inputStride outputBase bound t hsize hin))
  substitute (if backward then gates.reverse else gates)

theorem tickStridedHistoryQuantumLayers_payload (tm : Turing.FinTM2) (capacity input inputStride outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+inputStride*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) (backward : Bool) :
    ((if backward then (tickStridedHistoryRawNodes tm capacity input inputStride outputBase bound t).reverse
      else tickStridedHistoryRawNodes tm capacity input inputStride outputBase bound t).map (rawAssignmentPayload backward)).flatten=
      ((tickStridedHistoryQuantumLayers tm capacity input inputStride outputBase bound t wires hsize hin hout backward).map ShiBQP.encLayer).flatten :=
  rawProgramPayload_substitute _ _
    (tickStridedHistoryRawNodes_bounded tm capacity input inputStride outputBase bound t wires hsize hout)
    (tickStridedHistoryRawNodes_topological tm capacity input inputStride outputBase bound t hsize hin)
    (paddedIterationCompile_distinct_controls _ _ _ _ _ _) backward

theorem tickStridedHistoryQuantumLayers_length (tm : Turing.FinTM2) (capacity input inputStride outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+inputStride*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) (backward : Bool) (hc : 0 < capacity) :
    (tickStridedHistoryQuantumLayers tm capacity input inputStride outputBase bound t wires hsize hin hout backward).length=
      t*tickForestLayerCount tm capacity := by
  have h := rawProgram_substitute_length_both (tickStridedHistoryRawNodes tm capacity input inputStride outputBase bound t)
    (tickStridedHistoryRawNodes_bounded tm capacity input inputStride outputBase bound t wires hsize hout)
    (tickStridedHistoryRawNodes_topological tm capacity input inputStride outputBase bound t hsize hin)
    (paddedIterationCompile_distinct_controls _ _ _ _ _ _) backward
  simp only [tickStridedHistoryRawNodes,paddedIterationCompile_layerCount] at h
  rw [tickForestLayerCount_coordinates tm capacity hc]
  simpa only [tickStridedHistoryQuantumLayers,tickStridedHistoryRawNodes] using h

end ShiReversibleGenerator
