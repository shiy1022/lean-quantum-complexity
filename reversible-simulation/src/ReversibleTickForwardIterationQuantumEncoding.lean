import ReversibleTickIterationQuantumEncoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversible ShiReversibleGateBridge

noncomputable def tickForwardIterationQuantumLayers (tm : Turing.FinTM2) (capacity input outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+(bound+1)*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) : ShiShallow.Layered wires :=
  substitute (compileAssignments (boundProgram wires (tickIterationRawNodes tm capacity input outputBase bound t)
    (tickIterationRawNodes_bounded tm capacity input outputBase bound t wires hsize hout)
    (tickIterationRawNodes_topological tm capacity input outputBase bound t hsize hin)))

theorem tickForwardIterationQuantumLayers_payload (tm : Turing.FinTM2) (capacity input outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+(bound+1)*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) :
    ((tickIterationRawNodes tm capacity input outputBase bound t).map (rawAssignmentPayload false)).flatten=
      ((tickForwardIterationQuantumLayers tm capacity input outputBase bound t wires hsize hin hout).map ShiBQP.encLayer).flatten :=
  rawProgramPayload_substitute _ _
    (tickIterationRawNodes_bounded tm capacity input outputBase bound t wires hsize hout)
    (tickIterationRawNodes_topological tm capacity input outputBase bound t hsize hin)
    (paddedIterationCompile_distinct_controls _ _ _ _ _ _) false

theorem tickForwardIterationQuantumLayers_length (tm : Turing.FinTM2) (capacity input outputBase bound t wires : Nat)
    (hsize : tickSizeBound tm ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+(bound+1)*i.val < outputBase)
    (hout : outputBase+t*(configurationWidth tm capacity*(bound+1)) ≤ wires) (hc : 0 < capacity) :
    (tickForwardIterationQuantumLayers tm capacity input outputBase bound t wires hsize hin hout).length=
      t*tickForestLayerCount tm capacity := by
  have h := rawProgram_substitute_length_both (tickIterationRawNodes tm capacity input outputBase bound t)
    (tickIterationRawNodes_bounded tm capacity input outputBase bound t wires hsize hout)
    (tickIterationRawNodes_topological tm capacity input outputBase bound t hsize hin)
    (paddedIterationCompile_distinct_controls _ _ _ _ _ _) false
  simp only [tickIterationRawNodes,paddedIterationCompile_layerCount] at h
  rw [tickForestLayerCount_coordinates tm capacity hc]
  simpa only [Bool.false_eq_true,if_false,tickForwardIterationQuantumLayers,tickIterationRawNodes] using h

end ShiReversibleGenerator
