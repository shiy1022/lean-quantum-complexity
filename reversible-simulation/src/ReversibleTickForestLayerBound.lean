import ReversibleTickForestCircuitCertificate

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- A forest's exact elementary-layer count is linear in its number of bounded-size formulas. -/
theorem formulaListElementaryLayerCount_bound {ι : Type} (ps : List (Formula ι)) (bound : Nat)
    (hsize : ∀ p ∈ ps,p.size ≤ bound) :
    (ps.map (fun p => formulaElementaryLayers p+1)).sum ≤ ps.length*(37*bound+1) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have ht := ih (fun q hq => hsize q (by simp [hq]))
    have hp := formulaElementaryLayers_bound p
    have hs := Nat.mul_le_mul_left 37 (hsize p (by simp))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem tickForestLayerCount_bound (tm : Turing.FinTM2) (capacity : Nat) (hc : 0 < capacity) :
    tickForestLayerCount tm capacity ≤ configurationWidth tm capacity*(37*tickSizeBound tm+1) := by
  rw [tickForestLayerCount_coordinates tm capacity hc]
  simpa only [tickForest_length] using formulaListElementaryLayerCount_bound (tickForest tm capacity)
    (tickSizeBound tm) (tickForest_size tm capacity)

end ShiReversibleGenerator
