import ReversibleMachineCopyPayloadAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace ShiReversibleGenerator
open ShiReversible ShiReversibleTM ShiReversibleFormula ShiReversibleGateBridge

/-- Exact byte agreement between the actual serializer body and the original semantic quantum circuit. -/
theorem machineLengthPhaseBodyPayload_quantum (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) (hc : 0<c) :
    machineLengthPhaseBodyPayload tm e₀ e₁ c d n=
      ((paddedMachineQuantumCircuit tm e₀ e₁ n ((n+c)^d)).map ShiBQP.encLayer).flatten := by
  let cap := n+(n+c)^d*machinePushBound tm+1
  let ps := initialForest tm e₀ cap n
  let qs := tickForest tm cap
  let rs := extractionForest tm e₁ cap
  let nodes := paddedFinishedCompile ps qs rs (tickForest_length tm cap) 17 (tickSizeBound tm)
    (extractionBitBound tm cap) ((n+c)^d)
  let ht := fun a ha => (paddedFinishedCompile_interval ps qs rs (tickForest_length tm cap)
    17 (tickSizeBound tm) (extractionBitBound tm cap) ((n+c)^d)
    (initialForest_size tm e₀ cap n) (tickForest_size tm cap) (extractionForest_size tm e₁ cap) a ha).2
  let hp := paddedFinishedCompile_topological ps (initialForest_length tm e₀ cap n) qs rs
    (tickForest_length tm cap) 17 (tickSizeBound tm) (extractionBitBound tm cap) ((n+c)^d)
    (initialForest_size tm e₀ cap n) (tickForest_size tm cap) (extractionForest_size tm e₁ cap)
  let C := paddedRawOutputCircuit tm e₀ e₁ n ((n+c)^d)
  have hn : C.nodes=boundProgram _ nodes ht hp := rfl
  have he := SingleAssignmentCircuit.quantum_payload_raw C nodes ht hp
    (machineFinishedRawNodes_distinct_controls tm e₀ e₁ n ((n+c)^d)) hn
  have hb := machineLengthPhaseBodyPayload_raw tm e₀ e₁ c d n hc
  dsimp only at hb
  rw [outputCopyResourcePayload_semantic tm e₀ e₁ n ((n+c)^d)] at hb
  exact hb.trans he.symm

/-- The same circuit's depth is exactly the actual serializer's accumulated layer count. -/
theorem machineLengthPhaseBodyLayers_quantum (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) :
    machineLengthPhaseBodyLayers tm e₀ e₁ c d n=
      (paddedMachineQuantumCircuit tm e₀ e₁ n ((n+c)^d)).length := by
  let cap := n+(n+c)^d*machinePushBound tm+1
  let ps := initialForest tm e₀ cap n
  let qs := tickForest tm cap
  let rs := extractionForest tm e₁ cap
  let nodes := paddedFinishedCompile ps qs rs (tickForest_length tm cap) 17 (tickSizeBound tm)
    (extractionBitBound tm cap) ((n+c)^d)
  let ht := fun a ha => (paddedFinishedCompile_interval ps qs rs (tickForest_length tm cap)
    17 (tickSizeBound tm) (extractionBitBound tm cap) ((n+c)^d)
    (initialForest_size tm e₀ cap n) (tickForest_size tm cap) (extractionForest_size tm e₁ cap) a ha).2
  let hp := paddedFinishedCompile_topological ps (initialForest_length tm e₀ cap n) qs rs
    (tickForest_length tm cap) 17 (tickSizeBound tm) (extractionBitBound tm cap) ((n+c)^d)
    (initialForest_size tm e₀ cap n) (tickForest_size tm cap) (extractionForest_size tm e₁ cap)
  let C := paddedRawOutputCircuit tm e₀ e₁ n ((n+c)^d)
  have hn : C.nodes=boundProgram _ nodes ht hp := rfl
  have he := SingleAssignmentCircuit.quantum_layers_raw C nodes ht hp
    (machineFinishedRawNodes_distinct_controls tm e₀ e₁ n ((n+c)^d)) hn
  have hb := machineLengthPhaseBodyLayers_raw tm e₀ e₁ c d n
  dsimp only at hb
  apply hb.trans
  symm
  simpa only [paddedMachineQuantumCircuit,C,paddedRawOutputCircuit,nodes,ps,qs,rs,cap,extractionForest_length] using he

end ShiReversibleGenerator
