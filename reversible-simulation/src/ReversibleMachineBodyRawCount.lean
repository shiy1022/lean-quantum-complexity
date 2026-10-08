import ReversibleMachineBodyRawAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual accumulated layer total is exactly twice the original computation's elementary layers plus its output copies. -/
theorem machineLengthPhaseBodyLayers_raw (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) :
    let cap := n+(n+c)^d*machinePushBound tm+1
    let nodes := paddedFinishedCompile (initialForest tm e₀ cap n) (tickForest tm cap)
      (extractionForest tm e₁ cap) (tickForest_length tm cap) 17 (tickSizeBound tm)
      (extractionBitBound tm cap) ((n+c)^d)
    machineLengthPhaseBodyLayers tm e₀ e₁ c d n=
      2*(nodes.map rawAssignmentLayerCount).sum+(2*cap+1) := by
  dsimp only
  unfold machineLengthPhaseBodyLayers paddedFinishedCompile
  simp only [List.map_append,List.sum_append,paddedForestCompile_layerCount,paddedIterationCompile_layerCount]
  rw [←tickForestLayerCount_coordinates tm _ (by omega)]
  simp only [initializationCapacityPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,initializationForestLayerCount]
  ring

end ShiReversibleGenerator
