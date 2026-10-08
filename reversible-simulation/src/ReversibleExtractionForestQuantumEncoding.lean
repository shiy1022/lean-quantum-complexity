import ReversibleMachineExtraction
import ReversiblePaddedIterationElementaryLayers
import ReversibleRawSubstitutionLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversible ShiReversibleGateBridge

noncomputable def extractionForestRawNodes (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (capacity input inputStride outputBase bound : Nat) : List RawAssignment :=
  paddedForestCompile (fun i => input+inputStride*i.val) outputBase bound (extractionForest tm e capacity)

theorem extractionForestRawNodes_bounded (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : extractionBitBound tm capacity ≤ bound) (hout : outputBase+(2*capacity+1)*(bound+1) ≤ wires) :
    ∀ a ∈ extractionForestRawNodes tm e capacity input inputStride outputBase bound, a.target < wires := by
  intro a ha
  have h := (paddedForestCompile_interval (extractionForest tm e capacity) (fun i => input+inputStride*i.val)
    outputBase bound (fun p hp => (extractionForest_size tm e capacity p hp).trans hsize) a ha).2
  have ht : a.target < outputBase+(2*capacity+1)*(bound+1) := by
    simpa only [extractionForest_length] using h
  exact ht.trans_le hout

theorem extractionForestRawNodes_topological (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (capacity input inputStride outputBase bound : Nat)
    (hsize : extractionBitBound tm capacity ≤ bound) (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase) :
    ∀ a ∈ extractionForestRawNodes tm e capacity input inputStride outputBase bound, a.Topological :=
  paddedForestCompile_topological (extractionForest tm e capacity) (fun i => input+inputStride*i.val) outputBase bound
    (fun p hp => (extractionForest_size tm e capacity p hp).trans hsize) hin

noncomputable def extractionForestQuantumLayers (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : extractionBitBound tm capacity ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase)
    (hout : outputBase+(2*capacity+1)*(bound+1) ≤ wires) (backward : Bool) : ShiShallow.Layered wires :=
  let gates := compileAssignments (boundProgram wires (extractionForestRawNodes tm e capacity input inputStride outputBase bound)
    (extractionForestRawNodes_bounded tm e capacity input inputStride outputBase bound wires hsize hout)
    (extractionForestRawNodes_topological tm e capacity input inputStride outputBase bound hsize hin))
  substitute (if backward then gates.reverse else gates)

theorem extractionForestQuantumLayers_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : extractionBitBound tm capacity ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase)
    (hout : outputBase+(2*capacity+1)*(bound+1) ≤ wires) (backward : Bool) :
    ((if backward then (extractionForestRawNodes tm e capacity input inputStride outputBase bound).reverse
      else extractionForestRawNodes tm e capacity input inputStride outputBase bound).map (rawAssignmentPayload backward)).flatten =
      ((extractionForestQuantumLayers tm e capacity input inputStride outputBase bound wires hsize hin hout backward).map ShiBQP.encLayer).flatten :=
  rawProgramPayload_substitute _ _ (extractionForestRawNodes_bounded tm e capacity input inputStride outputBase bound wires hsize hout)
    (extractionForestRawNodes_topological tm e capacity input inputStride outputBase bound hsize hin)
    (paddedForestCompile_distinct_controls _ _ _ _) backward

theorem extractionForestQuantumLayers_length (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (capacity input inputStride outputBase bound wires : Nat)
    (hsize : extractionBitBound tm capacity ≤ bound)
    (hin : ∀ i : Fin (configurationWidth tm capacity), input+inputStride*i.val < outputBase)
    (hout : outputBase+(2*capacity+1)*(bound+1) ≤ wires) (backward : Bool) :
    (extractionForestQuantumLayers tm e capacity input inputStride outputBase bound wires hsize hin hout backward).length =
      ((extractionForest tm e capacity).map (fun p => formulaElementaryLayers p+1)).sum := by
  exact (rawProgram_substitute_length_both _ (extractionForestRawNodes_bounded tm e capacity input inputStride outputBase bound wires hsize hout)
    (extractionForestRawNodes_topological tm e capacity input inputStride outputBase bound hsize hin)
    (paddedForestCompile_distinct_controls _ _ _ _) backward).trans (paddedForestCompile_layerCount _ _ _ _)

end ShiReversibleGenerator
