import ReversibleMachineComponentRawPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The full actually printed body is compute-copy-uncompute of the original semantic raw assignment list, in exact quantum order. -/
theorem machineLengthPhaseBodyPayload_raw (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) (hc : 0<c) :
    let cap := n+(n+c)^d*machinePushBound tm+1
    let nodes := paddedFinishedCompile (initialForest tm e₀ cap n) (tickForest tm cap)
      (extractionForest tm e₁ cap) (tickForest_length tm cap) 17 (tickSizeBound tm)
      (extractionBitBound tm cap) ((n+c)^d)
    machineLengthPhaseBodyPayload tm e₀ e₁ c d n=
      rawNodesPayload false nodes++outputCopyResourcePayload tm n ((n+c)^d)++rawNodesPayload true nodes := by
  dsimp only
  have ht : 0<(n+c)^d := Nat.pow_pos (by omega)
  rw [machineFinishedRawNodes_decomposition tm e₀ e₁ n ((n+c)^d) ht]
  unfold machineLengthPhaseBodyPayload
  simp only [initializerResourcePayload_raw,tickResourcePayload_raw,extractionResourcePayload_raw,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  simp [rawNodesPayload,List.map_append,List.flatten_append,List.reverse_append,List.append_assoc]

end ShiReversibleGenerator
