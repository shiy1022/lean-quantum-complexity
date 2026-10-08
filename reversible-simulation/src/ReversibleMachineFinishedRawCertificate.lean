import ReversibleRawCleanCircuitCount

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Distinct conjunction controls are preserved across the original three-block semantic compiler. -/
theorem machineFinishedRawNodes_distinct_controls (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    let cap := n+budget*machinePushBound tm+1
    ∀ a ∈ paddedFinishedCompile (initialForest tm e₀ cap n) (tickForest tm cap) (extractionForest tm e₁ cap)
      (tickForest_length tm cap) 17 (tickSizeBound tm) (extractionBitBound tm cap) budget,a.DistinctControls := by
  dsimp only
  intro a ha
  unfold paddedFinishedCompile at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact paddedForestCompile_distinct_controls _ _ _ _ a ha
    · exact paddedIterationCompile_distinct_controls _ _ _ _ _ _ a ha
  · exact paddedForestCompile_distinct_controls _ _ _ _ a ha

end ShiReversibleGenerator
