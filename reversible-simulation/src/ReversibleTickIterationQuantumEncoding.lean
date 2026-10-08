import ReversiblePaddedIterationElementaryLayers
import ReversibleTickInverseAdvanceIterationPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversible ShiReversibleGateBridge

noncomputable def tickIterationRawNodes (tm : Turing.FinTM2) (capacity input outputBase bound t : Nat) : List RawAssignment :=
  paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound t
    (fun i => input+(bound+1)*i.val) outputBase

theorem tickIterationRawNodes_bounded (tm : Turing.FinTM2) (capacity input outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) :
    ∀ a ∈ tickIterationRawNodes tm capacity input outputBase bound t,a.target < wires := by
  intro a ha
  exact ((paddedIterationCompile_interval (tickForest tm capacity) (tickForest_length tm capacity) bound
    (fun p hp => (tickForest_size tm capacity p hp).trans hsize) t _ outputBase a ha).2).trans_le hout

theorem tickIterationRawNodes_topological (tm : Turing.FinTM2) (capacity input outputBase bound t : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+(bound+1)*i.val < outputBase) :
    ∀ a ∈ tickIterationRawNodes tm capacity input outputBase bound t,a.Topological :=
  paddedIterationCompile_topological (tickForest tm capacity) (tickForest_length tm capacity) bound
    (fun p hp => (tickForest_size tm capacity p hp).trans hsize) t _ outputBase hin

noncomputable def tickInverseIterationQuantumLayers (tm : Turing.FinTM2) (capacity input outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+(bound+1)*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) : ShiShallow.Layered wires :=
  substitute (compileAssignments (boundProgram wires (tickIterationRawNodes tm capacity input outputBase bound t)
    (tickIterationRawNodes_bounded tm capacity input outputBase bound t wires hsize hout)
    (tickIterationRawNodes_topological tm capacity input outputBase bound t hsize hin))).reverse

theorem tickInverseIterationQuantumLayers_payload (tm : Turing.FinTM2) (capacity input outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+(bound+1)*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) :
    ((tickIterationRawNodes tm capacity input outputBase bound t).reverse.map (rawAssignmentPayload true)).flatten=
      ((tickInverseIterationQuantumLayers tm capacity input outputBase bound t wires hsize hin hout).map ShiBQP.encLayer).flatten :=
  rawProgramPayload_substitute _ _
    (tickIterationRawNodes_bounded tm capacity input outputBase bound t wires hsize hout)
    (tickIterationRawNodes_topological tm capacity input outputBase bound t hsize hin)
    (paddedIterationCompile_distinct_controls _ _ _ _ _ _) true

theorem tickInverseIterationQuantumLayers_length (tm : Turing.FinTM2) (capacity input outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+(bound+1)*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) (hc : 0 < capacity) :
    (tickInverseIterationQuantumLayers tm capacity input outputBase bound t wires hsize hin hout).length=
      t*tickForestLayerCount tm capacity := by
  have h := rawProgram_substitute_length_both (tickIterationRawNodes tm capacity input outputBase bound t)
    (tickIterationRawNodes_bounded tm capacity input outputBase bound t wires hsize hout)
    (tickIterationRawNodes_topological tm capacity input outputBase bound t hsize hin)
    (paddedIterationCompile_distinct_controls _ _ _ _ _ _) true
  simp only [tickIterationRawNodes,paddedIterationCompile_layerCount] at h
  rw [tickForestLayerCount_coordinates tm capacity hc]
  simpa only [Bool.true_eq,if_true,tickInverseIterationQuantumLayers,tickIterationRawNodes] using h

end ShiReversibleGenerator
