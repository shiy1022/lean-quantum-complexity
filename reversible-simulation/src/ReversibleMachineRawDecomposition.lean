import ReversibleMachinePreparedCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The original semantic compiler is exactly the three raw compiler blocks used by the actual serializer. -/
theorem machineFinishedRawNodes_decomposition (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) (ht : 0<budget) :
    let cap := n+budget*machinePushBound tm+1
    let base := n+18*configurationWidth tm cap+budget*(configurationWidth tm cap*(tickSizeBound tm+1))
    paddedFinishedCompile (initialForest tm e₀ cap n) (tickForest tm cap) (extractionForest tm e₁ cap)
      (tickForest_length tm cap) 17 (tickSizeBound tm) (extractionBitBound tm cap) budget=
      initializationRawNodes tm e₀ cap n++
        tickStridedHistoryRawNodes tm cap (n+17) 18 (n+18*configurationWidth tm cap) (tickSizeBound tm) budget++
        extractionForestRawNodes tm e₁ cap
          (base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm)
          (tickSizeBound tm+1) base (extractionBitBound tm cap) := by
  dsimp only
  unfold paddedFinishedCompile initializationRawNodes tickStridedHistoryRawNodes extractionForestRawNodes
  rw [machinePreparedRead_strided tm e₀ _ n budget ht,machineInitialRead_strided tm _ n]
  simp only [initialForest_length]
  have h : ∀ w : Nat,n+w*(17+1)=n+18*w := by intro w; ring
  rw [h]

end ShiReversibleGenerator
